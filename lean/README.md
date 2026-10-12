# Verification library (Lean 4)

`BespokeVerify/Basic.lean` holds the lemmas that generated verification files rely on: a decidable
algebra of physical dimensions, and boundedness and smoothness of the regularised quotient used to
replace terms that could diverge.

    lake exe cache get   # fetch prebuilt Mathlib
    lake build

Files exported from the application are self-contained and can be checked with
`lake env lean <file>.lean` inside this project, or pasted into the Lean 4 web editor.
