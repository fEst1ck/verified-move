# Verified Move

The current goal of the project is to formalize the semantics of the move language, prove its key safety properties, and extract a provably correct bytecode verifier.

# Current Status
- [x] definitions
    - [x] types
    - [x] values
    - [x] memory model
- [ ] Operational semantics
    - [x] local instructions
    - [ ] global instructions
- [ ] Safety properties
    - [ ] type safety
    - [ ] reference safety
    - [ ] resource safety
        - [ ] define resource safety
            - [x] define tag-consistency: resource tags are unique
            - [ ] define resource intro/elim
        - [ ] prove tag-consistency is preserved by small step evaluation
            - [ ] mvloc
            - [x] cploc
            - [ ] ...
        - [ ] prove resource safety is preserved by small step evaluation
            - [ ] mvloc
            - [ ] cploc
            - [ ] ...
