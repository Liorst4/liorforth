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

\ See UnresolvedOperation in main.rs
: UnresolvedOperation::If    ( -- n ) 0 ;
: UnresolvedOperation::Else  ( -- n ) 1 ;
: UnresolvedOperation::While ( -- n ) 2 ;
: UnresolvedOperation::Leave ( -- n ) 3 ;

\ See ForthOperation in main.rs
: ForthOperation::PushData      ( n -- d ) 0 swap ;
: ForthOperation::CallEntry     ( a -- d ) 1 swap ;
: ForthOperation::BranchOnFalse ( n -- d ) 2 swap ;
: ForthOperation::Branch        ( a -- d ) 3 swap ;
: ForthOperation::CallPrimitive ( a -- d ) 4 swap ;
: ForthOperation::Return        ( -- d )   5 0    ;
: ForthOperation::Unresolved    ( n -- d ) 6 swap ; \ Use with UnresolvedOperation::*

: exit
  ForthOperation::Return
  latest-push
; immediate

: literal ( n -- )
  ForthOperation::PushData
  latest-push
; immediate

: if
  UnresolvedOperation::If ForthOperation::Unresolved
  postpone latest-push
; immediate

: then
  latest-last-unres-if-or-else
  dup >r
  latest-len swap - ForthOperation::BranchOnFalse
  r> latest!
; immediate

: else
  latest-last-unres-if-or-else

  \ Append unresolved else
  false postpone literal
  UnresolvedOperation::Else ForthOperation::Unresolved
  latest-push

  \ Edit unresolved if/else
  dup >r
  latest-len swap - ForthOperation::BranchOnFalse
  r> latest!
; immediate

: begin latest-len >cf ; immediate

: until
  latest-len cf> swap - ForthOperation::BranchOnFalse
  latest-push
; immediate

: while
  UnresolvedOperation::While ForthOperation::Unresolved
  latest-push
; immediate

: repeat
  \ Add a jump to the beginning of the word, at the end of the word
  \ (when the "while" condition is not met)
  false postpone literal
  cf> latest-len - ForthOperation::BranchOnFalse
  latest-push

  \ Add a jump to after the previously added jump in the place of
  \ the last unresolved "while"
  latest-len latest-last-unres-while
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
: create here postpone constant ;
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
  if
    type -2 throw
  else
    2drop
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

: fill ( c-addr u char -- )
  over 0= if 2drop drop exit then
  swap 0 do
    \ c-addr char
    over \ c-addr char c-addr
    i +  \ c-addr char c-addr+i
    over \ c-addr char c-addr+i char
    swap \ c-addr char char c-addr+i
    c!   \ c-addr char
  loop
  2drop
;

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

: align ( -- )
  here sizeof-cell mod dup 0= if
    drop
  else
    sizeof-cell swap - allot
  then
;

\ Since invoking words effects the stack itself,
\ the three commands r> dup and >r need to be
\ inline-d inside the word that uses r@
: r@ s" postpone r> postpone dup postpone >r " evaluate ; immediate

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
  r> ForthOperation::Branch
  latest-len 1 - latest! \ Replace the exit instruction with a branch one
;
