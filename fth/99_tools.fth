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

variable dump::row-size
$10 dump::row-size !

: dump::emit-byte ( c -- )
  dup $10 < if
    [char] 0 emit
  then
  .
;

: dump::emit-prefix-on-row-start ( addr n+:current-byte-offset -- )
  dup dump::row-size @ mod 0= if
    + . space
  else
    drop drop
  then
;

: dump::emit-newline-on-row-end ( n+:current-byte-offset -- )
  dump::row-size @ mod dump::row-size @ 1- = if
    cr
  then
;

: dump ( addr u -- )
  base @ >r hex \ Temporarily set base to hex

  0 do
    dup i dump::emit-prefix-on-row-start
    dup i + c@ dump::emit-byte
    i dump::emit-newline-on-row-end
    loop
  cr
  drop

  r> base ! \ Restore base
;
