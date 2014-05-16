#!/usr/bin/env perl
use strict;
use warnings;

use Test::More;
use Math::Prime::Util qw/twin_prime_count/;

# 2^n using primesieve (fast), double checked with Pari 2.7.0 (slow):
#   a(n)=my(s, p=2); forprime(q=3, 2^n, if(q-p==2, s++); p=q); s
#   for (i=1,35,print(2^i," ", a(i)))
# 10^n from tables
my %tpcvals = (
                   1 =>                    0,
                   2 =>                    0,
                   4 =>                    1,
                   8 =>                    2,
                  16 =>                    3,
                  32 =>                    5,
                  64 =>                    7,
                 128 =>                   10,
                 256 =>                   17,
                 512 =>                   24,
                1024 =>                   36,
                2048 =>                   62,
                4096 =>                  107,
                8192 =>                  177,
               16384 =>                  290,
               32768 =>                  505,
               65536 =>                  860,
              131072 =>                 1526,
              262144 =>                 2679,
              524288 =>                 4750,
             1048576 =>                 8535,
             2097152 =>                15500,
             4194304 =>                27995,
             8388608 =>                50638,
            16777216 =>                92246,
            33554432 =>               168617,
            67108864 =>               309561,
           134217728 =>               571313,
           268435456 =>              1056281,
           536870912 =>              1961080,
          1073741824 =>              3650557,
          2147483648 =>              6810670,
          4294967296 =>             12739574,
          8589934592 =>             23878645,
         17179869184 =>             44849427,
         34359738368 =>             84384508,
         68719476736 =>            159082253,
#        137438953472 =>            300424743,
                  10 =>                    2,
                 100 =>                    8,
                1000 =>                   35,
               10000 =>                  205,
              100000 =>                 1224,
             1000000 =>                 8169,
            10000000 =>                58980,
           100000000 =>               440312,
          1000000000 =>              3424506,
         10000000000 =>             27412679,
        100000000000 =>            224376048,
       1000000000000 =>           1870585220,
      10000000000000 =>          15834664872,
     100000000000000 =>         135780321665,
    1000000000000000 =>        1177209242304,
   10000000000000000 =>       10304195697298,
  100000000000000000 =>       90948839353159,
 1000000000000000000 =>      808675888577436,
);

plan tests => scalar(keys %tpcvals);

foreach my $n (sort {$a <=> $b} keys %tpcvals) {
  my $tpc = $tpcvals{$n};
  is( twin_prime_count($n), $tpc, "Pi_2($n) = $tpc" );
}