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
: variable create 0 , ;
: aligned
  dup sizeof-cell mod dup 0= if
  drop else
  sizeof-cell swap - +
  then ;
: nip swap drop ;
