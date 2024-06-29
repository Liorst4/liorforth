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

: <> ( n n -- f ) = invert ;
: 0<> ( n -- f ) 0 <> ;
: 0> ( n -- f ) 0 > ;
: u> ( u u -- f ) 2dup = >r u< r> or invert ;
: nip ( x1 x2 -- x2 ) swap drop ;
: tuck ( x1 x2 -- x2 x1 x2 ) swap over ;

: again
  false postpone literal
  postpone until
; immediate

: hex #16 base ! ;

\ Since invoking words effects the stack itself, commands are inline-d inside the caller
: 2>r ( x1 x2 -- ) s" postpone swap postpone >r postpone >r" evaluate ; immediate
: 2r> ( -- x1 x2 ) s" postpone r> postpone r> postpone swap" evaluate ; immediate
: 2r@ ( -- x1 x2 ) s" 2r> 2dup 2>r" evaluate ( no need to postpone since these are immediate ) ; immediate

: buffer: create allot ;
