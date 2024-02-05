( Copyright © 2022 Lior Stern. )

( This file is part of liorforth. )
( liorforth is free software: you can redistribute it and/or modify it under )
( the terms of the GNU General Public License as published by the Free Software )
( Foundation, either version 3 of the License, or any later version. )

( liorforth is distributed in the hope that it will be useful, but WITHOUT ANY )
( WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR )
( A PARTICULAR PURPOSE. See the GNU General Public License for more details. )

( You should have received a copy of the GNU General Public License along with )
( liorforth. If not, see <https://www.gnu.org/licenses/>. )

: exit
  5 0 \ ForthOperation::Return
  postpone push-latest
; immediate

: literal ( n -- )
  0 swap \ ForthOperation::PushCellToStack(...)
  postpone push-latest
; immediate

: if
  6 0 \ ForthOperation::Unresolved(UnresolvedOperation::If)
  postpone push-latest
; immediate

: while
  6 2 \ ForthOperation::Unresolved(UnresolvedOperation::While)
  postpone push-latest
; immediate

: leave
  s" postpone unloop" evaluate
  false postpone literal
  6 3 \ ForthOperation::Unresolved(UnresolvedOperation::Leave)
  postpone push-latest
; immediate

: 1+ 1 + ;
: 1- 1 - ;
: 0< 0 < ;
: 0= 0 = ;
: decimal 10 base ! ;
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

  swap over + swap ( c-addr+u u )
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
    s" postpone type" evaluate ( TODO: anyway better? )
  else
    type
  then
; immediate

: abort-with-message ( f c-addr u -- )
  rot
  if
    type abort
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

: loop 1 postpone literal postpone +loop ; immediate

: fill ( c-addr u char -- )
  over 0= if 2drop drop exit then
  swap 0 do
    ( c-addr char )
    over ( c-addr char c-addr )
    i +  ( c-addr char c-addr+i )
    over ( c-addr char c-addr+i char )
    swap ( c-addr char char c-addr+i )
    c!   ( c-addr char )
  loop
  2drop
;

: abs ( n -- n )
  dup 0 < if
    negate
  then
;

: select-compare ( x1 x2 xt -- x1|x2 )
  >r 2dup r> ( x1 x2 x1 x2 xt )
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

( Since invoking words effects the stack itself, )
( the three commands r> dup and >r need to be )
( inline-d inside the word that uses r@ )
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
