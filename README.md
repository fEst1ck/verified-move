# Verified Move

The current goal of the project is to formalize the semantics of the move language in Coq, prove its key safety properties, and extract a provably correct bytecode verifier.

# Documentation

The definitions used in the project are documented in more readable form in `document.*`.

# Requirement

Coq version: 8.16.

# Current Status

The lastest development is currently on the tag-consistent branch.

- [x] definitions
    - [x] types
    - [x] values
    - [x] memory model
- [ ] static semantics
    - [ ] borrow checking rules
    - [ ] type checking rules
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
