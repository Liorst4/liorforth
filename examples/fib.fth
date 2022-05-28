: print-top dup . cr ;

: upper-limit 1000000 ;

: fibonacci
  0 print-top
  1 print-top
  begin
    over over +
    print-top
    rot drop
    dup upper-limit > until
;

fibonacci
bye
