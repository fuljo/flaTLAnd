----------------------------- MODULE LiveClock -----------------------------

EXTENDS Clock

LSpec == Clock /\ WF_vars(Next)

AlwaysTick == []<><<Next>>_vars
AllTimes == \A h \in 0..23, m \in 0..59 : []<>(hr = h /\ min = m)

=============================================================================
\* Modification History
\* Last modified Sun May 03 12:04:20 CEST 2020 by edomora97
\* Created Sun May 03 11:21:38 CEST 2020 by edomora97
