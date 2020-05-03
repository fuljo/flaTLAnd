------------------------------- MODULE Clock -------------------------------

EXTENDS Naturals
VARIABLE hr, min

vars == <<hr, min>>

Init == hr \in (0..23) /\ min \in (0..59) \*hr = 0 /\ min = 0

NextMin == min' = IF min < 59
                  THEN min + 1
                  ELSE 0

NextHr == hr' = IF min < 59
                THEN hr
                ELSE IF hr < 23
                     THEN hr + 1
                     ELSE 0
 
Next == NextMin /\ NextHr

Clock == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Sun May 03 12:06:35 CEST 2020 by edomora97
\* Created Sun May 03 11:18:43 CEST 2020 by edomora97
