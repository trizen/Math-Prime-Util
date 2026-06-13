/***********    inverse_sigma0_list   and   inverse_sigma0_count    ***********/

#include <string.h>
#define FUNC_isqrt 1
#define FUNC_is_perfect_square 1
#define FUNC_log2floor 1
#include "ptypes.h"
#include "cache.h"
#include "constants.h"
#include "factor.h"
#include "inverse_sigma0.h"
#include "prime_counts.h"
#include "primality.h"
#include "sieve.h"
#include "sort.h"
#include "util.h"

/*
 * Given a range [lo,hi] and a k value, returns or counts all the values
 * in the range that have a divisor count equal to k.
 *
 * 1) SIEVE
 *    A lightweight segmented sieve.  It tracks only the divisor count and
 *    residual value for each integer in the segment, not the full factor list.
 *    When sieving to sqrt(hi) is cheap, residual values are prime.  Otherwise
 *    we sieve through cuberoot(hi), after which each residual has at most two
 *    prime factors, so classifying it as 1, prime, prime square, or semiprime
 *    is enough.
 *
 * 2) GENERATE
 *    We enumerate all ordered factorizations of k into factors >= 2 drawn
 *    from divisors of k, treating each factorization as a "prime signature"
 *    (sorted descending exponent list).  For each signature we generate or
 *    count numbers in [lo,hi] with that exact prime factorization shape.
 *
 *    The generate/count recursion closely follows the reference Perl
 *    implementation (inverse_tau_in_range.pl / count_of_inverse_tau_in_range.pl)
 *    with these key optimizations carried over:
 *
 *    a) rem_sum bound: at each recursion level, hi_prime = rootint(B/m, rem_sum)
 *       where rem_sum is the sum of ALL remaining exponents.  This is tighter
 *       than rootint(B/m, e) because every subsequent prime is also >= p.
 *
 *    b) @seen deduplication: when the remaining signature has repeated exponents,
 *       we skip processing the same exponent value more than once per level,
 *       avoiding redundant subtrees.
 *
 *    c) pn_primorial lower bound: the smallest number with k distinct prime
 *       factors is 2*3*5*...*p_k, so lo = max(lo, pn_primorial(k)).
 *
 *    d) Count k==1 base case: prime_count_range(lo, hi) -- one O(1) lookup.
 *
 *    e) Count k==2 base case: for each outer prime p, the inner count is
 *       prime_count(rootint(n/m/p^e, e2)) - prime_count(p), giving the
 *       number of primes q with p < q <= rootint(n/m/p^e, e2).
 *
 *    f) List k==1 (last-slot) tight lo: the minimum prime p satisfies
 *       m*p^e >= lo, so p >= ceil_root(ceil_div(lo,m), e).  We take the
 *       max of this and the previously used prime + 1.
 */

#ifndef INVERSE_SIGMA0_TAU_MAX_WIDTH
#define INVERSE_SIGMA0_TAU_MAX_WIDTH UVCONST(10000000)
#endif

#ifndef INVERSE_SIGMA0_TAU_MAX_CHUNKED_WIDTH
#define INVERSE_SIGMA0_TAU_MAX_CHUNKED_WIDTH UVCONST(100000000)
#endif

#if BITS_PER_WORD == 64
#ifndef INVERSE_SIGMA0_TAU_CHUNK_MIN_LO
#define INVERSE_SIGMA0_TAU_CHUNK_MIN_LO UVCONST(100000000000)
#endif
#endif

/******************************************************************************/
/* Sieve path (unchanged)                                                      */
/******************************************************************************/

static bool full_factor_sieve(UV sqrtn, UV range)
{
  if (sqrtn <    1000000U) return (range > 200000);
  if (sqrtn <   10000000U) return (range > 300000);
  if (sqrtn <   35000000U) return (range > 350000);
  if (sqrtn <  100000000U) return (range > 500000);
  if (sqrtn <  350000000U) return (range > 750000);
  if (sqrtn < 1000000000U) return (range > 1000000);
  if (sqrtn < 3500000000U) return (range > 1500000);
  return (range > 2000000);
}

static int first_multiple_in_range(UV *A, UV lo, UV hi, UV p)
{
  UV a = (lo / p) * p;
  if (a < lo) {
    if (a > UV_MAX - p) return 0;
    a += p;
  }
  if (a > hi) return 0;
  *A = a;
  return 1;
}

static void tau_update(uint16_t *tau, UV k, UV mult)
{
  UV t;
  if (*tau == 0) return;
  t = *tau;
  if (mult == 0 || t > k / mult) { *tau = 0; return; }
  t *= mult;
  *tau = (k % t != 0) ? 0 : (uint16_t)t;
}

static void tau_update_residual(uint16_t *tau, UV k, UV rem, bool full_sieve)
{
  UV need;
  if (*tau == 0 || rem <= 1) return;
  if (k % *tau != 0) { *tau = 0; return; }
  need = k / *tau;
  if (full_sieve) {
    *tau = (need == 2) ? (uint16_t)k : 0;
  } else if (need == 2) {
    *tau = is_def_prime(rem)                               ? (uint16_t)k : 0;
  } else if (need == 3) {
    *tau = is_perfect_square(rem)                          ? (uint16_t)k : 0;
  } else if (need == 4) {
    *tau = (!is_perfect_square(rem) && !is_def_prime(rem)) ? (uint16_t)k : 0;
  } else {
    *tau = 0;
  }
}

static UV* tau_sieve(UV *count, UV lo, UV hi, UV k, bool count_only)
{
  UV range, sqrthi, sievelim, j, len, alloc, *rem, *list;
  uint16_t *tau;
  bool full_sieve;

  range = hi - lo + 1;
  sqrthi = isqrt(hi);
  full_sieve = full_factor_sieve(sqrthi, hi - lo);
  sievelim = full_sieve ? sqrthi : icbrt(hi);

  len = alloc = 0;
  list = 0;
  New(0, rem, range, UV);
  New(0, tau, range, uint16_t);
  for (j = 0; j < range; j++) { rem[j] = lo + j; tau[j] = 1; }

  START_DO_FOR_EACH_PRIME(2, sievelim) {
    UV A, idx;
    if (first_multiple_in_range(&A, lo, hi, p)) {
      for (idx = A - lo; idx < range; idx += p) {
        UV e = 0;
        if (tau[idx] == 0) continue;
        while ((rem[idx] % p) == 0) { e++; rem[idx] /= p; }
        if (e > 0) tau_update(&tau[idx], k, e + 1);
      }
    }
  } END_DO_FOR_EACH_PRIME

  for (j = 0; j < range; j++) {
    if (tau[j] != 0 && rem[j] > 1)
      tau_update_residual(&tau[j], k, rem[j], full_sieve);
    if (tau[j] == k) {
      if (count_only) {
        len++;
      } else {
        if (len >= alloc) {
          if (alloc == 0) { alloc = 32; New(0, list, alloc, UV); }
          else            { alloc *= 2; Renew(list, alloc, UV);  }
        }
        list[len++] = lo + j;
      }
    }
  }

  Safefree(tau);
  Safefree(rem);
  *count = len;
  return list;
}

static UV* tau_sieve_chunked(UV *count, UV lo, UV hi, UV k, bool count_only)
{
  UV len = 0, alloc = 0, seglo = lo, *list = 0;

  while (seglo <= hi) {
    UV segcount, seghi, *seglist;
    seghi = (hi - seglo + 1 > INVERSE_SIGMA0_TAU_MAX_WIDTH)
          ? seglo + INVERSE_SIGMA0_TAU_MAX_WIDTH - 1 : hi;
    seglist = tau_sieve(&segcount, seglo, seghi, k, count_only);
    if (count_only) {
      len += segcount;
    } else if (segcount > 0) {
      if (len + segcount > alloc) {
        alloc = (alloc == 0) ? 32 : alloc;
        while (len + segcount > alloc) alloc *= 2;
        if (list == 0) New(0, list, alloc, UV);
        else           Renew(list, alloc, UV);
      }
      Copy(seglist, list + len, segcount, UV);
      len += segcount;
    }
    Safefree(seglist);
    if (seghi == hi) break;
    seglo = seghi + 1;
  }
  *count = len;
  return list;
}

static bool use_tau_sieve(UV lo, UV hi, UV k)
{
  UV width = hi - lo + 1;
  if (k > 65535) return 0;
  if (width <= INVERSE_SIGMA0_TAU_MAX_WIDTH) return 1;
#if BITS_PER_WORD == 64
  if (lo >= INVERSE_SIGMA0_TAU_CHUNK_MIN_LO &&
      width <= INVERSE_SIGMA0_TAU_MAX_CHUNKED_WIDTH) return 1;
#endif
  return 0;
}

/******************************************************************************/
/* Helpers shared by count and list paths                                      */
/******************************************************************************/

static UV ceil_div_uv(UV n, UV d)
{
  return n / d + ((n % d) != 0);
}

static UV ceil_root_uv(UV n, uint32_t k)
{
  UV r;
  if (n <= 1 || k <= 1) return n;
  r = rootint(n, k);
  return r + (ipowsafe(r, k) < n);
}

/* m * p^e, returning 0 on overflow past limit */
static UV mul_pow_limit(UV m, UV p, UV e, UV limit)
{
  while (e-- > 0) {
    if (p == 0 || m > limit / p) return 0;
    m *= p;
  }
  return m;
}

/******************************************************************************/
/* Count path                                                                  */
/*                                                                             */
/* count_sig(n, m, lo, sig, nsig, j):                                         */
/*   Count integers x <= n of the form  x = m * q0^sig[0] * q1^sig[1] * ...  */
/*   where q0 < q1 < ... are primes, all >= lo, and distinct from each other. */
/*   sig[] is the REMAINING signature (exponents), sorted descending.          */
/*   j = number of primes already used that are < lo (= prime_count(lo-1)).   */
/*                                                                             */
/* This directly mirrors count_prime_signature_numbers() in the Perl script.  */
/******************************************************************************/

static UV count_sig(UV n, UV m, UV lo, const UV *sig, int nsig, UV j);

static UV count_sig(UV n, UV m, UV lo, const UV *sig, int nsig, UV j)
{
  UV rem_sum, hi, count, seen_e, e, e2, i;
  int k = nsig;

  if (k == 0 || m == 0) return 0;

  /* rem_sum = sum of all remaining exponents.
   * hi = rootint(n/m, rem_sum): the largest prime p we can assign at this
   * level such that m * p^e * (p+1)^e2 * ... <= n is still possible.
   * Using rem_sum (not just sig[0]) is the key tightening from the Perl code:
   *   $hi = rootint(divint($n, $m), $rem_sum) */
  rem_sum = 0;
  for (i = 0; i < (UV)k; i++) rem_sum += sig[i];
  if (rem_sum == 0) return 0;

  if (m > n / 2) return 0;  /* quick overflow guard before division */
  hi = rootint(n / m, rem_sum);
  if (lo > hi) return 0;

  count = 0;
  seen_e = 0; /* bitmask / value tracking for @seen dedup */

  for (i = 0; i < (UV)k; i++) {
    UV local_j, p, new_sig[MPU_MAX_FACTORS];
    int nk, ni;

    e = sig[i];

    /* @seen deduplication: skip if we already processed this exponent value
     * at this recursion level.  Mirrors:  next if $seen[$e]++  */
    if (i > 0 && sig[i] == sig[i-1]) continue;

    /* Build new_sig = sig[] with element i removed */
    nk = 0;
    for (ni = 0; ni < k; ni++)
      if (ni != (int)i) new_sig[nk++] = sig[ni];

    local_j = j;

    if (k == 1) {
      /* Base case k==1: count primes p in [lo, hi].
       * prime_count(hi) - j  where j = prime_count(lo-1).
       * Equivalent to prime_count_range(lo, hi). */
      UV cnt = prime_count(hi);
      count += (cnt > local_j) ? cnt - local_j : 0;

    } else if (k == 2) {
      /* Base case k==2: mirrors the Perl forprimes + prime_count($u) - ++$local_j.
       * For each outer prime p in [lo, hi]:
       *   t = m * p^e
       *   u = rootint(n/t, e2)
       *   inner count = prime_count(u) - local_j  (primes > p and <= u)
       *   then ++local_j to account for p itself being used */
      e2 = new_sig[0];
      START_DO_FOR_EACH_PRIME(lo, hi) {
        UV t = mul_pow_limit(m, p, e, n);
        if (t == 0) break;
        {
          UV u   = (e2 == 1) ? n / t : rootint(n / t, e2);
          UV cnt = prime_count(u);
          if (cnt > local_j) count += cnt - local_j;
          local_j++;
        }
      } END_DO_FOR_EACH_PRIME

    } else {
      /* General case: iterate outer primes, recurse */
      UV new_rem_sum = 0;
      UV ni2;
      for (ni2 = 0; ni2 < (UV)nk; ni2++) new_rem_sum += new_sig[ni2];

      for (p = lo; p <= hi; p = next_prime(p)) {
        UV t = mul_pow_limit(m, p, e, n);
        UV r;
        if (t == 0) break;
        r = next_prime(p);
        count += count_sig(n, t, r, new_sig, nk, local_j++);
      }
    }
  }

  return count;
}

/******************************************************************************/
/* List path                                                                   */
/*                                                                             */
/* list_sig(lo_range, hi_range, m, lo_prime, sig, nsig, out_list, out_count): */
/*   Generate all x in [lo_range, hi_range] of the form                       */
/*   x = m * q0^sig[0] * q1^sig[1] * ... with q0 < q1 < ... primes >= lo_p.  */
/*                                                                             */
/* Mirrors prime_signature_numbers_in_range() in the Perl script.             */
/******************************************************************************/

typedef struct {
  UV  lo;
  UV  hi;
  UV  count;
  UV  alloc;
  UV *list;
} list_out_t;

static void list_record(list_out_t *out, UV v)
{
  if (out->count >= out->alloc) {
    if (out->alloc == 0) { out->alloc = 32; New(0, out->list, out->alloc, UV); }
    else                 { out->alloc *= 2; Renew(out->list, out->alloc, UV);  }
  }
  out->list[out->count++] = v;
}

static void list_sig(UV lo_range, UV hi_range, UV m, UV lo_prime,
                     const UV *sig, int nsig, list_out_t *out)
{
  UV rem_sum, hi, seen_e, e, e2, i;
  int k = nsig;

  if (k == 0 || m == 0) return;

  rem_sum = 0;
  for (i = 0; i < (UV)k; i++) rem_sum += sig[i];
  if (rem_sum == 0) return;

  if (m > hi_range) return;
  hi = rootint(hi_range / m, rem_sum);
  if (lo_prime > hi) return;

  seen_e = 0;

  for (i = 0; i < (UV)k; i++) {
    UV p, new_sig[MPU_MAX_FACTORS];
    int nk, ni;

    e = sig[i];

    /* @seen deduplication */
    if (i > 0 && sig[i] == sig[i-1]) continue;

    /* Build new_sig = sig[] with element i removed */
    nk = 0;
    for (ni = 0; ni < k; ni++)
      if (ni != (int)i) new_sig[nk++] = sig[ni];

    if (k == 1) {
      /* Last slot: tight lower bound.
       * Need m * p^e >= lo_range  =>  p >= ceil_root(ceil_div(lo_range,m), e)
       * Also p must be >= lo_prime (the next prime after the last used prime).
       * Mirrors:  my $lo_tight = vecmax($lo, rootint_ceil(cdivint($A,$m),$e)) */
      UV lo_tight;
      if (m < lo_range) {
        UV need = ceil_div_uv(lo_range, m);
        lo_tight = (e == 1) ? need : ceil_root_uv(need, (uint32_t)e);
      } else {
        lo_tight = 2;
      }
      if (lo_tight < lo_prime) lo_tight = lo_prime;
      if (lo_tight < 2) lo_tight = 2;
      if (lo_tight > hi) continue;

      START_DO_FOR_EACH_PRIME(lo_tight, hi) {
        UV v = mul_pow_limit(m, p, e, hi_range);
        if (v != 0 && v >= lo_range && v <= hi_range)
          list_record(out, v);
      } END_DO_FOR_EACH_PRIME

    } else {
      /* Recurse: iterate outer primes in [lo_prime, hi] */
      for (p = lo_prime; p <= hi; p = next_prime(p)) {
        UV t = mul_pow_limit(m, p, e, hi_range);
        if (t == 0) break;
        list_sig(lo_range, hi_range, t, next_prime(p), new_sig, nk, out);
      }
    }
  }
}

/******************************************************************************/
/* Partition enumeration (tau_partitions)                                      */
/*                                                                             */
/* Enumerate all sorted-descending exponent lists (prime signatures) whose    */
/* product (each exponent + 1) equals k, with sum of exponents <= max_sum_e.  */
/*                                                                             */
/* Mirrors tau_partitions() in both Perl scripts exactly:                      */
/*   - Divisors of k (>= 2) are the allowed factor values.                    */
/*   - Factors chosen in non-decreasing order (=> reversed = descending exp). */
/*   - Loop: for each divisor d of k with d <= target, d >= min_d,            */
/*     if target % d == 0, recurse with target/d.                              */
/*   - When target == 1, emit the accumulated signature.                       */
/******************************************************************************/

typedef void (*sig_cb_t)(void *data, const UV *sig, int nsig);

typedef struct {
  UV       max_sum_e;
  UV      *divs;      /* divisors of k that are >= 2, in ascending order */
  int      ndivs;
  UV       path[MPU_MAX_FACTORS]; /* factors-1, in non-decreasing order */
  int      pathlen;
  sig_cb_t callback;
  void    *cb_data;
} part_ctx_t;

static void partition_recurse(part_ctx_t *ctx, UV target, int min_idx,
                              UV curr_sum_e)
{
  int i;

  if (target == 1) {
    /* path[0..pathlen-1] are exponents in non-decreasing order.
     * Reverse to get descending order for the signature. */
    UV sig[MPU_MAX_FACTORS];
    int len = ctx->pathlen, j;
    for (j = 0; j < len; j++) sig[j] = ctx->path[len - 1 - j];
    ctx->callback(ctx->cb_data, sig, len);
    return;
  }

  if (ctx->pathlen >= MPU_MAX_FACTORS) return;

  /* Mirror of Perl:
   *   for my $i ($min_idx .. $end) {
   *     my $d = $divs[$i];
   *     last if $d > $target;
   *     last if ($curr_sum_e + $e > $max_sum_e);
   *     if ($target % $d == 0) { push @path, $e; recurse; pop @path; }
   *   }
   * Note: the Perl loop goes up to $target (not sqrt($target)), so all
   * divisors including $target itself are tried here. */
  for (i = min_idx; i < ctx->ndivs; i++) {
    UV d = ctx->divs[i];
    UV e = d - 1;
    if (d > target) break;                          /* sorted, nothing bigger */
    if (curr_sum_e + e > ctx->max_sum_e) break;     /* e only grows, stop */
    if (target % d != 0) continue;
    ctx->path[ctx->pathlen++] = e;
    partition_recurse(ctx, target / d, i, curr_sum_e + e);
    ctx->pathlen--;
  }
}

static void enumerate_signatures(UV k, UV max_sum_e,
                                 sig_cb_t callback, void *cb_data)
{
  part_ctx_t ctx;
  UV ndivs_all, skip, *all_divs;

  if (k == 0) return;
  if (k == 1) { callback(cb_data, NULL, 0); return; }

  all_divs = divisor_list(k, &ndivs_all, k);

  /* Skip divisor 1 */
  skip = 0;
  while (skip < ndivs_all && all_divs[skip] < 2) skip++;

  ctx.max_sum_e = max_sum_e;
  ctx.divs      = all_divs + skip;
  ctx.ndivs     = (int)(ndivs_all - skip);
  ctx.pathlen   = 0;
  ctx.callback  = callback;
  ctx.cb_data   = cb_data;

  partition_recurse(&ctx, k, 0, 0);
  Safefree(all_divs);
}

/******************************************************************************/
/* Callbacks                                                                   */
/******************************************************************************/

/* For count_inverse_tau: count integers <= n with given prime signature.
 * Mirrors count_prime_signature_numbers($n, $sig) in the Perl script. */
typedef struct { UV n; UV count; } count_data_t;

static void count_callback(void *data, const UV *sig, int nsig)
{
  count_data_t *d = (count_data_t *)data;
  UV sum_e, i;

  if (nsig == 0) { if (d->n >= 1) d->count++; return; }

  sum_e = 0;
  for (i = 0; i < (UV)nsig; i++) sum_e += sig[i];
  if (sum_e == 0 || sum_e > log2floor(d->n)) return;

  /* pn_primorial check: smallest number with nsig distinct prime factors
   * is 2*3*5*...*p_nsig.  If that already exceeds n, skip.
   * Mirrors: $n >= 1 || return 0  and the implicit pn_primorial pruning. */
  d->count += count_sig(d->n, 1, 2, sig, nsig, 0);
}

/* For list_inverse_tau: collect integers in [lo,hi] with given signature.
 * Mirrors prime_signature_numbers_in_range($A, $B, $sig) in the Perl script. */
typedef struct { UV lo; UV hi; list_out_t *out; } list_data_t;

static void list_callback(void *data, const UV *sig, int nsig)
{
  list_data_t  *d   = (list_data_t *)data;
  list_out_t   *out = d->out;
  UV lo = d->lo, hi = d->hi;
  UV sum_e, min_val, i, p;

  if (nsig == 0) {
    if (lo <= 1 && 1 <= hi) list_record(out, 1);
    return;
  }

  sum_e = 0;
  for (i = 0; i < (UV)nsig; i++) sum_e += sig[i];
  if (sum_e == 0 || sum_e > log2floor(hi)) return;

  /* pn_primorial lower bound: raise lo to at least pn_primorial(nsig).
   * Mirrors: $A = vecmax(pn_primorial($k), $A) */
  min_val = pn_primorial((UV)nsig);
  if (min_val == 0 || min_val > hi) return;  /* overflow or impossible */
  if (lo < min_val) lo = min_val;
  if (lo > hi) return;

  /* Minimum achievable value with smallest primes: 2^s0 * 3^s1 * ... */
  min_val = 1; p = 0;
  for (i = 0; i < (UV)nsig; i++) {
    p = ((int)(i+1) < NPRIMES_SMALL) ? primes_small[i+1] : next_prime(p);
    min_val = mul_pow_limit(min_val, p, sig[i], hi);
    if (min_val == 0) return;
  }
  if (min_val > hi) return;

  list_sig(lo, hi, 1, 2, sig, nsig, out);
}

/******************************************************************************/
/* Public API                                                                  */
/******************************************************************************/

UV inverse_sigma0_count(UV lo, UV hi, UV k)
{
  UV max_sum_e;

  if (k == 0 || hi < 1 || k > hi) return 0;
  if (k == 1) return (lo <= 1 && hi >= 1) ? 1 : 0;
  if (k == 2) return prime_count_range(lo, hi);
  if (lo < 1) lo = 1;
  if (lo > hi) return 0;

  if (use_tau_sieve(lo, hi, k)) {
    UV count;
    tau_sieve_chunked(&count, lo, hi, k, 1);
    return count;
  }

  /* count(lo,hi,k) = count_upto(hi,k) - count_upto(lo-1,k) */
  max_sum_e = log2floor(hi);
  {
    count_data_t cbd_hi = { hi, 0 };
    count_data_t cbd_lo = { lo - 1, 0 };
    UV count_hi, count_lo;

    enumerate_signatures(k, max_sum_e, count_callback, &cbd_hi);
    count_hi = cbd_hi.count;

    if (lo <= 1) return count_hi;

    enumerate_signatures(k, log2floor(lo - 1), count_callback, &cbd_lo);
    count_lo = cbd_lo.count;

    return (count_hi > count_lo) ? count_hi - count_lo : 0;
  }
}

UV* inverse_sigma0_list(UV *count, UV lo, UV hi, UV k)
{
  list_out_t  out;
  list_data_t cbd;

  *count = 0;
  if (k == 0 || hi < 1 || k > hi) return 0;
  if (k == 1) {
    UV *list;
    if (lo <= 1 && hi >= 1) {
      New(0, list, 1, UV);
      list[0] = 1; *count = 1;
      return list;
    }
    return 0;
  }
  if (k == 2) {
    UV *list;
    if (hi < 2) return 0;
    *count = range_prime_sieve(&list, (lo < 2) ? 2 : lo, hi);
    return list;
  }
  if (lo < 1) lo = 1;
  if (lo > hi) return 0;
  if (use_tau_sieve(lo, hi, k))
    return tau_sieve_chunked(count, lo, hi, k, 0);

  memset(&out, 0, sizeof(out));
  cbd.lo  = lo;
  cbd.hi  = hi;
  cbd.out = &out;

  enumerate_signatures(k, log2floor(hi), list_callback, &cbd);

  if (out.count > 1) {
    size_t len = out.count;
    sort_dedup_uv_array(out.list, 0, &len);
    out.count = len;
  }
  *count = out.count;
  return out.list;
}
