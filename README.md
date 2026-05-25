# accumulative-typestate
A Coq (Rocq) formalization of accumulative typestate system

## How to Build the Project

1. Generate the Makefile:
   ```sh
   coq_makefile -f _CoqProject -o Makefile
   ```
2. Build the project:
   ```sh
   make
   ```

# Dependency
Works on Coq 8.20.0.

RegLang version 1.2.2