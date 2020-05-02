# flaTLAnd
Presentation of the TLA+ tool for the course of Formal Methods @Polimi

- Introduction
    - What is TLA+
    - Motivation for using A high-level specification language:
        good for designing algorithms and protocols upfront, rather than making
        assertion on their implementations
    - How it works
    - Who uses TLA+
        - AWS
        - Intel for HW
    - What is inside the TLA+ Toolbox
- First Example
    - Live coding inside TLA+ Toolbox
    - TODO: choose first example
- 2-Phase commit
    - Definition of the Resource Managers
    - Actual protocol with Transaction Manager
    - `TCWrong == <> \E r1 \in RM : rmState[r1] = "committed"`
- **Remark** bounded model checking on demand
