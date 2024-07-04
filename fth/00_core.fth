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
: UnresolvedOperation::If    ( -- n ) 0 ;
: UnresolvedOperation::Else  ( -- n ) 1 ;
: UnresolvedOperation::While ( -- n ) 2 ;
: UnresolvedOperation::Leave ( -- n ) 3 ;

\ See pop_forth_operation in main.rs
: ForthOperation::PushData      ( -- n ) 0 ;
: ForthOperation::CallEntry     ( -- n ) 1 ;
: ForthOperation::BranchOnFalse ( -- n ) 2 ;
: ForthOperation::CallPrimitive ( -- n ) 3 ;
: ForthOperation::Next          ( -- n ) 4 ;
: ForthOperation::Unresolved    ( -- n ) 5 ; \ Use with UnresolvedOperation::*
: ForthOperation::PushFloat     ( -- n ) 6 ;

: postpone
  ' ForthOperation::CallEntry latest-push
; immediate

: exit
  ForthOperation::Next
  latest-push
; immediate

: literal ( n -- )
  ForthOperation::PushData
  latest-push
; immediate

: if ( -- n )
  UnresolvedOperation::If ForthOperation::Unresolved
  latest-push

  \ Save the offset of the unresolved operation on stack
  latest-len 1 -
; immediate

: then ( n -- )
  latest-len over - ForthOperation::BranchOnFalse
  rot latest!
; immediate

: else ( n -- n )
  \ Append unresolved else
  false postpone literal \ The following unresolved else will be replaced with a
                         \ "BranchOnFalse", adding a false to make it an
                         \ "unconditional" jump
  UnresolvedOperation::Else ForthOperation::Unresolved
  latest-push

  \ Save offset of unresolved else
  latest-len 1 - >r

  \ Edit previous unresolved if/else
  latest-len over - ForthOperation::BranchOnFalse
  rot latest!

  r> \ Move offset of unresolved else to data stack
; immediate

: begin latest-len >cf ; immediate

: until
  latest-len cf> swap - ForthOperation::BranchOnFalse
  latest-push
; immediate

: while
  UnresolvedOperation::While ForthOperation::Unresolved
  latest-push
  cf>
  latest-len 1 -
  >cf
  >cf
; immediate

: repeat
  \ Add a jump to the beginning of the word, at the end of the word
  \ (when the "while" condition is not met)
  false postpone literal
  cf> latest-len - ForthOperation::BranchOnFalse
  latest-push

  \ Add a jump to after the previously added jump in the place of
  \ the last unresolved "while"
  latest-len cf>
  dup >r
  -
  ForthOperation::BranchOnFalse
  r>
  latest!

  \ This one is a bit confusing, I recommend creating a word
  \ that uses a "repeat" loop, and inspecting the results with "see"
  \ to get a better understanding on what is going on here
; immediate

: leave
  s" postpone unloop" evaluate
  false postpone literal
  UnresolvedOperation::Leave ForthOperation::Unresolved
  latest-push
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

: ['] ' postpone literal ; immediate

: ."
  postpone s"
  state @ if
    s" postpone type" evaluate \ TODO: anyway better?
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
  s" postpone abort-with-message" evaluate
; immediate

: spaces ( n -- )
  dup 0= if drop exit then
  begin space 1- dup 0= until
  drop
;

: do ( n n -- )
  state @ if
    s" postpone do" evaluate
    latest-len >cf
  else
    swap >cl
  then
; immediate

: i ( -- n ) cl> 2dup >cl drop ;
: j ( -- n ) cl> cl> over >r >cl >cl r> ;
: unloop cl> 2drop ;
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
: r@ s" postpone r> postpone dup postpone >r " evaluate ; immediate

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

