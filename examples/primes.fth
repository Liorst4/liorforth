: prime_candidate here 1 cells - ;
: divisor here 2 cells - ;

: prime?
  true
  2 divisor !
  begin
    prime_candidate @ divisor @ mod 0 = if
      drop
      false
      prime_candidate @ divisor !
    then
    1 divisor +!
    divisor @ prime_candidate @ < invert until
;

: upper_limit 10000 ;

: primes
  1 . cr
  2 . cr
  3 . cr
  5 . cr
  7 . cr
  9 prime_candidate !
  begin
    prime? if prime_candidate @ . cr then
    2 prime_candidate +!
    prime_candidate @ upper_limit > until
;

2 cells allot
primes
bye
