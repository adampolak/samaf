# Simulated Annealing for Maximum-Alignment Forest

This solver uses simulated annealing to compute the maximum agreement forest (MAF) between a pair
of rooted binary trees in Newick format. It was developed for the heuristick track of PACE 2026.

The solver is implemented in a single standalone C++ file with no external dependencies. Compile it with:
```
g++ solver.cpp -o solver -O3 -std=c++17
```