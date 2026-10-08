# Benchmarks

`mystic_bench` is the primary consumer benchmark.

## Running it

```sh
taskset -c 2,3 cargo bench --bench mystic_bench
```

Pin to both SMT siblings of one P-core if on a machine with P+E cores.

## Premise

The mystic bench simulates repeated asking of if certain variables can be true,
followed by refinement with new clauses added and re-asking.

## The corpus

`test_cases/mystic6x6/` holds 48 instances captured from one complete 6x6
generation run, sampled from the full set to spread evenly
over the `can_pos` time range and to include all four selection phases:

### Header

Beyond ordinary DIMACS comments, `c query <start> <end>` records the half-open
variable range `can_pos` was called with, in 0-based variable indices
(what `can_pos` takes — *not* the 1-based literal numbering used in the clause body).
For this corpus it is `0..216` throughout.
