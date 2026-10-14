# BatteriesKMP

Knuth-Morris-Pratt (KMP) matchers for Lean 4, as a Batteries cell.

KMP locates every occurrence of a pattern in an input in time linear in the length of the input,
after a preprocessing step linear in the length of the pattern. The preprocessed matcher can be
reused to search for the same pattern in many inputs.

- `BatteriesKMP.Matcher` provides the generic machinery in the `KMP` namespace:
  `KMP.PrefixTable`, built from a pattern array or stream by `KMP.mkPrefixTable` and
  `KMP.mkPrefixTableOfStream`, and `KMP.Matcher`, which runs over any finite `Std.Stream` with
  `KMP.Matcher.next?`. The iterator transformer `KMP.Matcher.Iterator` turns an iterator into one
  that yields the iterator state just after each match, and is finite whenever the inner iterator
  is.
- `BatteriesKMP.Array` provides `Array.Matcher` with `find?` and `findAll`, which return start
  and end positions of matching infix subarrays, and the shortcuts `Array.findInfix?`,
  `Array.findAllInfix` and `Array.containsInfix`.
- `BatteriesKMP.List` provides `List.Matcher` with `find?` and `findAll`, which return start and
  end positions of matching infix sublists, and the shortcuts `List.findInfix?`,
  `List.findAllInfix` and `List.containsInfix`.
- `BatteriesKMP.String` provides `String.Matcher` with `find?` and `findAll`, which return
  matching `String.Slice`s, and the shortcuts `String.Slice.findInfix?`,
  `String.Slice.findAllInfix`, `String.Slice.containsInfix`, `String.findInfix?` and
  `String.findAllInfix`. The characters of a slice `s` are read as a finite stream of
  positions `s.Pos`.

All occurrences are reported, including overlapping ones.

```lean
import BatteriesKMP

#eval [0, 1, 1, 0, 1, 1, 0].findAllInfix [0, 1, 1, 0]    -- #[(0, 4), (3, 7)]
#eval #[0, 1, 1, 0, 1, 1, 0].findAllInfix #[0, 1, 1, 0]  -- #[(0, 4), (3, 7)]
#eval [2, 1, 1, 0, 1, 1, 2].containsInfix [0, 1, 1, 0]    -- false

def m := String.Matcher.ofString "abba"
#eval (m.findAll "abbabbabba").size                     -- 3
#eval (m.find? "aabbaa").isSome                         -- true
```

## Usage

Add the cell to your `lakefile.toml`:

```toml
[[require]]
name = "batteries-kmp"
git = "https://github.com/fgdorais/batteries-kmp"
rev = "main"
```

Stream matchers work over finite streams from
[batteries-finite-streams](https://github.com/fgdorais/batteries-finite-streams).

The `main` branch tracks the Lean toolchain of Batteries `main`. The `nightly-testing` branch
tracks Batteries `nightly-testing`.

## Acknowledgements

These matchers were developed in Batteries (formerly Std) and moved to this cell by
[batteries#1955][1]:

- [std4#178][2] by François G. Dorais: KMP prefix tables and matchers for arrays and strings.
- [batteries#823][3] by Kim Morrison: string matchers split into their own file.
- [batteries#1065][4] by François G. Dorais: KMP frontend for lists.
- [batteries#1398][5] by François G. Dorais: iterator transformer for KMP matchers.
- [batteries#1999][6] and [batteries#2000][7] by Taksh Kothari: iterators advance from their
  current state, and empty list patterns match at every boundary.

[1]: https://github.com/leanprover-community/batteries/pull/1955
[2]: https://github.com/leanprover-community/batteries/pull/178
[3]: https://github.com/leanprover-community/batteries/pull/823
[4]: https://github.com/leanprover-community/batteries/pull/1065
[5]: https://github.com/leanprover-community/batteries/pull/1398
[6]: https://github.com/leanprover-community/batteries/pull/1999
[7]: https://github.com/leanprover-community/batteries/pull/2000

---

Copyright (c) 2023 François G. Dorais. Released under the Apache 2.0 license, see
[LICENSE](LICENSE).
