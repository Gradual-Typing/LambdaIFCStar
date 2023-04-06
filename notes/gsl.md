# Experiments on GSLRef

The [GSLRef](https://pleiad.cl/gradual-security/) prototype

### Example 1 (rejected)

Under `gc = high`, the program is statically rejected:
```
ref_H true_L
```

Why?? To double check:
```
let a : Ref_B Bool_H = ref_H true_L in
  unit
```

### Example 2 (errors)

Under `gc = low`, the following program type-checks:
```
let y : (Ref_B Bool_?) = ref true_L in
let a : Unit = y := false_H in
  ! y
```

The `?` is to make the program type-check.
It errors at runtime:
```
Runtime security error: consistent transitivity between
⟨𝖡𝗈𝗈𝗅𝖧,𝖡𝗈𝗈𝗅[𝖧,⊤]⟩ and ⟨𝖡𝗈𝗈𝗅𝖫,𝖡𝗈𝗈𝗅𝖫⟩ is undefined
```

The program won't error in a dynamic system like $\lambda^{\mathit{info}}$,
because $\lambda^{\mathit{info}}$ allows upgrading a cell from `low` to
`high` under `pc = low`.
