\ Copyright © 2024 Lior Stern.

\ This file is part of liorforth.
\ liorforth is free software: you can redistribute it and/or modify it under
\ the terms of the GNU General Public License as published by the Free Software
\ Foundation, either version 3 of the License, or any later version.

\ liorforth is distributed in the hope that it will be useful, but WITHOUT ANY
\ WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
\ A PARTICULAR PURPOSE. See the GNU General Public License for more details.

\ You should have received a copy of the GNU General Public License along with
\ liorforth. If not, see <https://www.gnu.org/licenses/>.

\ See pop_forth_operation in main.rs
: ForthOperation::PushData      ( -- n ) 0 ;
: ForthOperation::CallEntry     ( -- n ) 1 ;
: ForthOperation::CallPrimitive ( -- n ) 2 ;
: ForthOperation::Next          ( -- n ) 3 ;
: ForthOperation::PushFloat     ( -- n ) 4 ;

: compile, ( xt -- ) ForthOperation::CallEntry latest-push ;

: postpone
  ' compile,
; immediate

: exit
  ForthOperation::Next
  latest-push
; immediate

: literal ( n -- )
  ForthOperation::PushData
  latest-push
; immediate

\ Select between two items in the data stack
\ When the given condition is true, only "a" remains on top of the stack
\ When the given condition is false, only "b" remains on top of the stack
: select ( x:a x:b f:cond -- x:a|b )
  invert 1 and roll drop
;

\ Add the given operation offset to the return address
\ Offset can be a negative number as well
: branch-relative ( n:op-offset -- )
                  ( r: addr:return-address -- addr:return-address-plus-offset )
  sizeof-forth-operation *
  r> + >r
;

\ When the given condition is **false**, add the given operation offset to the return address
\ Offset can be a negative number as well
: branch-relative? ( f:condition n:op-offset -- )
                   ( r: addr:return-address -- addr:return-address-plus-offset|return-address )
  0 swap
  sizeof-forth-operation *
  rot select
  r> + >r
;

: ['] ' postpone literal ; immediate

: unresolved-if-push -1 throw ;

: if ( -- n:offset-of-unresolved-push )
  ['] unresolved-if-push compile,

  \ Save the offset of the unresolved operation on stack
  latest-len 1 -

  ['] branch-relative? compile,
; immediate

: then ( n:offset-of-unresolved-push -- )
  latest-len over 2 + - ForthOperation::PushData
  rot latest!
; immediate

: unresolved-else-push -1 throw ;

: else ( n:offset-of-unresolved-if-push -- n:offset-of-unresolved-else-push )

  \ Append code to the end of the "if" clause to skip the "else" clause
  ['] unresolved-else-push compile,
  latest-len 1 - >r \ Save unresolved push for later
  ['] branch-relative compile,

  \ Resolve the "if" clause branch
  latest-len over 2 + - \ Calculate the offset for the branch in the "if" clause
  ForthOperation::PushData rot latest!

  r> \ Move offset of unresolved else to data stack
; immediate

: begin ( cf: -- n:offset-of-first-instruction-in-loop-body )
  latest-len >cf
; immediate

: until ( cf: n:offset-of-first-instruction-in-loop-body -- )
  latest-len 2 + cf> swap - ForthOperation::PushData latest-push
  ['] branch-relative? compile,
; immediate

: unresolved-while-push  -1 throw ;

: while ( cf: n:a -- n:b n:a )
        ( a -> offset-of-first-instruction-in-loop-body )
        ( b -> offset-of-unresolved-while-push )
  ['] unresolved-while-push compile,
  cf>
  latest-len 1 -
  ['] branch-relative? compile,
  >cf
  >cf
; immediate

: repeat ( cf: n:b n:a -- )
         ( a -> offset-of-first-instruction-in-loop-body )
         ( b -> offset-of-unresolved-while-push )

  \ Append a branch to the beginning of the loop
  cf> latest-len 2 + - postpone literal
  ['] branch-relative compile,

  \ Resolve the push for the branch in while
  \ Add an exit
  cf> dup latest-len swap 2 + - ForthOperation::PushData rot latest!
; immediate

: 1+ 1 + ;
: 1- 1 - ;
: 0< 0 < ;
: 0= 0 = ;
: decimal #10 base ! ;
: cells sizeof-cell * ;
: cell+ sizeof-cell + ;
: , here 1 cells allot ! ;
: chars sizeof-char * ;
: char+ sizeof-char + ;
: c, here 1 chars allot c! ;
: cr nl emit ;
: space bl emit ;
: / /mod swap drop ;
: +! dup @ swap rot rot + swap ! ;
: ?dup dup dup 0= if drop then ;
: 2drop drop drop ;
: 2dup over over ;
: 2swap rot >r rot >r r> r> ;
: 2over >r >r 2dup r> r> 2swap ;
: constant : postpone literal postpone ; ;
: align ( -- )
  here sizeof-cell mod dup 0= if
    drop
  else
    sizeof-cell swap - allot
  then
;
: create align here postpone constant ;
: variable create 0 , ;
: aligned
  dup sizeof-cell mod dup 0= if
  drop else
  sizeof-cell swap - +
  then ;
: nip swap drop ;
: 2* 2 * ;
: 2/ 2 / ;
: 2@ dup cell+ @ swap @ ;
: 2! swap over ! cell+ ! ;

: type ( c-addr u -- )
  dup 0= if
    2drop
    exit
  then

  swap over + swap \ c-addr+u u
  begin
    2dup - @ emit
    1 -
    dup 0 = until
  2drop
;

: [ false state ! ; immediate
: ] true state ! ;

: count ( addr -- addr c ) dup 1+ swap c@ ; \ See `CountedString` in main.rs
: char bl word count drop c@ ;
: [char] char postpone literal ; immediate

: ."
  postpone s"
  state @ if
    ['] type compile,
  else
    type
  then
; immediate

: abort -1 throw ;

: abort-with-message ( f c-addr u -- )
  rot
  0 = if
    2drop
  else
    type -2 throw
  then
;

: abort"
  postpone s"
  ['] abort-with-message compile,
; immediate

: spaces ( n -- )
  dup 0= if drop exit then
  begin space 1- dup 0= until
  drop
;

: do:start ( n:limit n:start-index -- )
           ( cl: -- d:starting-state )
  swap >cl
;

: do ( cf: -- u:amount-of-leave-instructions u:offset-of-the-loop-in-the-body )
  ['] do:start compile,
  0 >cf
  latest-len >cf
; immediate

: i ( -- n:iteration-index )
    ( cl: d:state -- d:state )
  cl> 2dup >cl
  drop
;

: j ( -- n:iteration-index )
    ( cl d:outer-loop-state d:inner-loop-state -- d:outer-loop-state d:inner-loop-state )
  cl> cl>
  over >r
  >cl >cl
  r>
;

: unloop ( cl: d:state -- )
  cl> 2drop
;

: unresolved-leave-push -1 throw ;

: leave ( cf: u:x*y u:y u:z -- u:x*[y+1] u:[y+1] u:z )
        \ x - offset of leave instruction
        \ y - amount of leave instructions
        \ z - offset of do loop
  ['] unloop compile,
  ['] unresolved-leave-push compile,
  cf> >r
  cf> 1 + >r
  latest-len 1 - >cf
  r> >cf
  r> >cf
  ['] branch-relative compile,
; immediate


: +loop:resolve-leaves ( cf: u:x*y u:y -- )
                       \ x - offset of leave instruction
                       \ y - amount of leave instructions
  \ Iterate over all "leave" instances
  cf> begin
    dup 0 > while
    1 -

    \ Write a jump to the end of the loop
    cf>
    dup latest-len swap 2 + - ForthOperation::PushData
    rot latest!

  repeat drop
;

: +loop:push-branch-to-start ( cf: n:do-start -- n:do-start )
  cf> latest-len 2 + - postpone literal
  ['] branch-relative? compile,
;

: +loop:over? ( -- f:loop-done )
              ( cl: d:state -- d:state )
  cl> 2dup >cl
  < invert
;

: +loop:update ( n:addition -- )
               ( cl: d:state -- d:new-state )
  cl> >r + r> >cl
;

: +loop:discard-state ( cl: d:state -- )
  cl> 2drop
;

: +loop:update-and-check-if-done ( n:addition -- f:loop-done )
                                 ( cl: d:state -- )
  +loop:update
  +loop:over? dup if
    +loop:discard-state
  then
;


: +loop
  ['] +loop:update-and-check-if-done compile,
  +loop:push-branch-to-start
  +loop:resolve-leaves
; immediate

: loop 1 postpone literal postpone +loop ; immediate

: abs ( n -- n )
  dup 0 < if
    negate
  then
;

: select-compare ( x1 x2 xt -- x1|x2 )
  >r 2dup r> \ x1 x2 x1 x2 xt
  execute if
  else
    swap
  then
  drop
;
: min ( x1 x2 -- x1|x2 )
  ['] < select-compare
;
: max ( x1 x2 -- x1|x2 )
  ['] > select-compare
;

: s>d ( n -- d )
  1 m*
;

: */mod ( n n n -- n n )
  >r m* r>
  sm/rem
;

: */ ( n n n -- n )
  */mod nip
;

\ Since invoking words effects the stack itself,
\ the three commands r> dup and >r need to be
\ inline-d inside the word that uses r@
: r@
  ['] r> compile,
  ['] dup compile,
  ['] >r compile,
; immediate

: fill ( c-addr u char -- )
  >r
  0 do
    r@ over i + c!
  loop
  r>
  2drop
;

\ create a temporary counted string in "here"
: tmp-counted ( addr n -- addr )
  dup here !
  here 1 + swap move
  here
;

MAX-CHAR constant /COUNTED-STRING
MAX-N constant RETURN-STACK-CELLS
MAX-N constant STACK-CELLS
false constant FLOORED
\ TODO: /HOLD and /PAD
: environment?
  tmp-counted find 0= if
    drop
    false
  else
    execute
    true
  then
;

\ Pushes the part that comes after `does>` to the end of the latest word
\ Use the part before the `does>` to `create` a new word
\ Kind of like a constructor
: does>
  \ Crate an arbitrary jump by replacing the `Next` at the end of the latest word with:
  \ * push data (address) instruction
  \ * call >r instruction
  \ * Next instruction
  \ The address pushed is what comes after `does>` in the calling word
  \ Moving this address from the return stack also prevents the environment from
  \ executing the rest of the calling word (the stuff after `does>`)

  r> ForthOperation::PushData latest-len 1 - latest!
  ['] >r ForthOperation::CallEntry latest-push
  ForthOperation::Next latest-push
;

