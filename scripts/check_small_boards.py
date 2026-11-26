"""Enumerate small king-grid matchings directly, allowing at most two axial edges."""

from functools import lru_cache
from math import comb


def enumerate_counts(height, width):
    """Return the counts with zero, one and two axial edges, in that order."""
    full = (1 << (height * width)) - 1
    neighbors = []
    for index in range(height * width):
        row, col = divmod(index, width)
        forward = []
        for dr, dc in ((0, 1), (1, -1), (1, 0), (1, 1)):
            r, c = row + dr, col + dc
            if r < height and 0 <= c < width:
                forward.append((1 << (r * width + c), int(dr == 0 or dc == 0)))
        neighbors.append(forward)

    @lru_cache(maxsize=None)
    def match(free, budget):
        if free == 0:
            return (1,) + (0,) * budget
        first = free & -free
        result = [0] * (budget + 1)
        # Earlier cells are covered, so the first free cell has only forward options.
        for partner, axial in neighbors[first.bit_length() - 1]:
            if free & partner and axial <= budget:
                tail = match(free ^ first ^ partner, budget - axial)
                for count, multiplicity in enumerate(tail, start=axial):
                    result[count] += multiplicity
        return tuple(result)

    result = match(full, 2)
    match.cache_clear()
    return result


def main():
    print("board       A0    A1    A2")
    for m in range(5):
        for n in range(5):
            counts = enumerate_counts(2 * m, 2 * n)
            expected = (1, 0, n * comb(m + 1, 2) + m * comb(n + 1, 2))
            if counts != expected:
                raise SystemExit(f"{2*m}x{2*n}: got {counts}, expected {expected}")
            if (m == n and m > 0) or (m, n) == (2, 3):
                print(f"{2*m}x{2*n:<5} {counts[0]:5} {counts[1]:5} {counts[2]:5}")
    print("PASS: 25 rectangles (half-dimensions 0 through 4).")


if __name__ == "__main__":
    main()
