This is the code for the paper "A Monad for Nonconstructivity"

### Sections 2 and 6 - base.v.

The names in the formalization correspond to those in the paper except:
- Double negation "[]" is `PClassical`
    - `Preturn` and `Pbind`
- The nonconstructivity monad is `Classical`
    - `Creturn` and `Cbind`
- The principle `[a = b] -> a = b` is `removedneq`

### Section 3 - cauchy.v

The bottom of the file has all of the proven theorems collected together in a series of `Check`s.

### Section 4 - quotient.v and reals.v

The definition of quotients is in `quotient.v`, and Section 4.1 is in `reals.v`.

`reals.v` also has a series of `Check`s at the bottom the file to show what has been proven.

### Section 5 - recursion.v