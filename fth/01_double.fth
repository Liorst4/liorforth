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

: 2constant ( x1 x2 -- )
  create , ,
  does> ( -- x1 x2 )
        2@
;

: 2variable ( x1 x2 -- )
  create 0 , 0 ,
;

: 2literal ( x1 x2 -- )
  swap postpone literal postpone literal
; immediate

: d= ( d d -- f )
  >r swap >r
  =
  r> r>
  =
  and
;

: d0= ( d -- f )
  0. d=
;
