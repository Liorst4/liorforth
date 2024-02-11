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

variable dump-row-size
$10 dump-row-size !
: dump ( addr u -- )
  base @ rot rot
  16 base !
  0 do
    i dump-row-size @ mod 0= if
      dup i + . space
    then

    dup i + c@
    dup $10 < if
      [char] 0 emit
    then
    .

    i dump-row-size @ mod dump-row-size @ 1- = if
      cr
    then

    loop

  drop

  base !

  cr
;
