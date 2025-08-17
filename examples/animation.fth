60                                   constant frames-per-second
10                                   constant seconds-to-play
1000 frames-per-second /             constant ms-to-sleep
seconds-to-play 1000 * ms-to-sleep / constant iterations


: render-frame ( n -- )
  80 mod 0 do bl emit loop
  ." hello there" cr
;

: play
  iterations 0 do
    i render-frame
    ms-to-sleep ms
  loop
;

play
