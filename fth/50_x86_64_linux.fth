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

: execute-syscall::setup-args ( x*amount-of-arguments:arguments n+:syscall-number n+:amount-of-arguments -- n+:syscall-number n+*6:arguments )
  swap >r
  6 swap - 0 do 0 loop
  r>
  6 0 do 6 roll loop
;

: execute-syscall::process-ret ( u:ret1 u:ret2 n:amount-of-return-values -- n*amount-of-return-values:return-values )
  1 = if
    drop
  then
;

: execute-syscall ( x*amount-of-arguments:arguments n+:syscall-number n+:amount-of-arguments n+:amount-of-return-values )
  >r execute-syscall::setup-args
  syscall
  r> execute-syscall::process-ret
;

: syscall: ( n+:syscall-number n+:amount-of-arguments n+:amount-of-return-values "<spaces>name" -- )
  create , , ,
  does> ( x*amount-of-arguments:arguments -- x*amount-of-return-values )
        dup 2 cells + @ swap
        dup 1 cells + @ swap
                      @
        execute-syscall
;

0 3 1 syscall: SYS_read
1 3 1 syscall: SYS_write
2 3 1 syscall: SYS_open
3 1 1 syscall: SYS_close
