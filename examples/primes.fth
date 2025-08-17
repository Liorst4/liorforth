1000000 constant upper_limit
: divisible? ( n n -- f ) mod 0= ;
: one-or-two ( n -- f ) dup 1 = swap 2 = or ;
: prime? ( n -- f )
  dup one-or-two if drop true then

  dup 1 - 2 do
    dup i divisible? if
       drop
       false
       unloop
       exit
    then
  loop

  drop
  true
;
: primes
  upper_limit 1 do
    i dup prime? if
      . cr
    else
      drop
    then
  loop
;

primes
