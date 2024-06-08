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

: begin-structure ( -- struct-size-ptr:addr 0:n )
  here 0
  create 0 ,
  does> ( -- n:struct-size )
        @
;

: end-structure ( struct-size-ptr:addr struct-size:n -- )
  aligned
  swap !
;

: +field ( n:struct-current-size n:bytes-to-add -- n:struct-updated-size )
  create
  over ,
  +
  does> ( addr -- addr )
       @ +
;

: cfield: 1 chars +field ;
: field: aligned 1 cells +field ;
: ffield: faligned 1 floats +field ;
