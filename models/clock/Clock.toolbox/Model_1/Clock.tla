------------------------------- MODULE Clock -------------------------------

EXTENDS Naturals
VARIABLE hr

Init == hr = 1
Next == hr' = IF hr /= 12 THEN hr + 1 ELSE 1

=============================================================================
\* Modification History
\* Last modified Sun May 03 11:20:11 CEST 2020 by edomora97
\* Created Sun May 03 11:18:43 CEST 2020 by edomora97
