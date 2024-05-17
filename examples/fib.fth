1000000 constant upper-limit

: print-top dup . cr ;

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
