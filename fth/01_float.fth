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

: f0< 0e f< ;
: fnegate -1e f* ;

\ NOTE: Takes argument from the floating point stack!
: fliteral
  ForthOperation::PushFloat
  latest-push
; immediate

: fconstant : postpone fliteral postpone ; ;

: fvariable
  create
  here
  1 allot falign
  0e f!
;

: float+ ( addr -- addr ) 1 + faligned ;

: floats sizeof-float * ;
