#!/usr/bin/env python3
"""Independent exhaustive checks of the finite F_2^3 identities used in the Lean proof."""
from itertools import product

GAMMA = range(8)  # 3-bit vectors; addition in F_2^3 is xor.

def add(a: int, b: int) -> int:
    return a ^ b

def functional(mask: int, vector: int) -> int:
    return (mask & vector).bit_count() & 1

def main() -> None:
    for A, B, p in product(GAMMA, repeat=3):
        PA = {A, add(A, p)}
        PB = {B, add(B, p)}
        assert (PA == PB) == (add(A, B) in (0, p))
        if p != 0:
            assert len(PA) == 2

    evenness_cases = 0
    for t, x, y, s in product(GAMMA, repeat=4):
        z = add(x, y)
        if x != 0 and y != 0 and z != 0:
            sides = (
                {t, add(t, x)},
                {add(t, x), add(add(t, x), y)},
                {t, add(t, z)},
            )
            count = sum(s in side for side in sides)
            assert count in (0, 2)
            evenness_cases += 1

    parity_cases = 0
    for x, y in product(GAMMA, repeat=2):
        z = add(x, y)
        if x == 0 or y == 0 or z == 0:
            continue
        for eta_a, eta_b, eta_c in product(GAMMA, repeat=3):
            # Linear functionals on F_2^3 are represented by dot-product masks.
            if eta_a ^ eta_b ^ eta_c != 0:
                continue
            if functional(eta_a, x) != 0:
                continue
            if functional(eta_b, y) != 0:
                continue
            if functional(eta_c, z) != 0:
                continue
            lhs = functional(eta_b, x)
            rhs = (int(eta_a != 0) + int(eta_b != 0) + int(eta_c != 0)) & 1
            assert lhs == rhs
            parity_cases += 1

    print('pair-set criteria: 512 exhaustive triples passed')
    print(f'local evenness: {evenness_cases} exhaustive cases passed')
    print(f'local dual parity: {parity_cases} admissible exhaustive cases passed')

if __name__ == '__main__':
    main()
