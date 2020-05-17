------------------------------- MODULE Clock -------------------------------

EXTENDS Naturals
VARIABLE hr, min

vars == <<hr, min>>
\******
Init == hr = 0 /\ min = 0
\*******
AdvanceMin == min' = IF min < 59
                     THEN min + 1
                     ELSE 0
\*******
AdvanceHr == hr' = IF min < 59
                   THEN hr
                   ELSE IF hr < 23
                        THEN hr + 1
                        ELSE 0
Tick == AdvanceMin /\ AdvanceHr
\** run verification
\********
Clock == Init /\ [][Tick]_vars
\** SPECIFICATION Clock
\** run verification

=============================================================================
\* Modification History
\* Last modified Sun May 03 12:07:47 CEST 2020 by edomora97
\* Created Sun May 03 11:18:43 CEST 2020 by edomora97
