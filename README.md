# `poly`: a WIP compiler

## An example that works rn

```sml
let
  fun id x = let val y = x in y end
  fun f (g : forall a. a -> a) = 3 + g 4
in f id end
```

This parses, typechecks, and is lowered to the polymorphic IR.

## Language features

**One-sentence summary:** an ML with higher-rank polymorphism, typeclasses, and
SML-inspired syntax.

**A more in-depth checklist:**
 - [X] Functions
 - [X] Polymorphism, let generalization, and the value restriction
    - [ ] Relaxed value restriction: track function arity and eta-expand
          point-free definitions if possible and needed
 - [X] Higher-rank (predicative) polymorphism and polymorphic subtyping
 - [X] Integers
 - [ ] Strings and other primitive types
 - [ ] ADTs and pattern matching (to do next)
 - [ ] Records
 - [ ] Haskell98-style typeclasses
 - [ ] Higher-kinded types
 - [ ] Modules, maybe

Note: no polymorphic recursion, GADTs, or existentials, since they make
monomorphisation impossible (or if not impossible, at least a lot harder).

## Compiler pipeline

**One-sentence summary:** whole-program compilation with optional
monomorphization and defunctionalization.

**A more in-depth checklist:**

**Parser** (in `Src`):
 - Works, mostly
 - Could use some tidying up
 - Produces a `Src.Exp` AST

**Elaborator** (in `Elab` and `ElabUtils`):
 - Works, mostly
 - Consumes the `Src.Exp` AST and produces `Poly.Exp` IR
 - Internally, uses its own `ElabUtils.Ty` and translates it from/to `Src.Ty`
   and `Poly.Ty`

**Polymorphic IR** (in `Poly`):
 - A typed ANF IR with System F-style explicit type application and abstraction
 - Type-preserving ANF optimizations on the IR
    - Nothing is implemented yet
    - [ ] Eta-contraction
    - [ ] Constant propagation, beta reduction
    - [ ] Inlining and DCE
    - [ ] Stretch goal: commuting conversions and join points
    - [ ] Stretch goal: user-defined rewrite rules

**Monomorphic IR** (unimplemented):
 - A (mostly) typed monomorphic (ANF? SSA?) IR
 - Two ways to get there:
    - Type erasure: replace polymorphic type variables with the boxed `any`
      type, and use dictionary passing for typeclasses
    - Monomorphization: this will be fairly complex due to higher-rank
      polymorphism.  However, by restricting first-class polymorphic values to
      have function type, it's doable alongside whole-program
      defunctionalization for first-class polymorphic functions.
 - More optimizations:
    - [ ] Contification
    - [ ] Inlining
    - [ ] DCE
    - [ ] Conditional constant propagation
    - [ ] Stretch goal: SROA, maybe others

**Backend** (unimplemented):
 - To do
 - For a first pass I will probably emit C or use LLVM, but it'd be cool to
   implement native codegen
 - Design decision: need an efficient implementation of currying






