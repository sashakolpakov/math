import OAI.AlgebraicTopology.Cohomology.Singular.Functor
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Algebra.Homology.Functor

/-! # Singular Presheaf -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf

noncomputable section

/-!
# Singular cochains on open subsets

This file constructs the actual presheaf of singular cochain complexes on a
space: an open set receives the singular cochains of its subspace topology,
and restriction is pullback along the continuous inclusion. It also constructs
the corresponding complex of module-valued presheaves. These are presheaves;
no sheaf condition or comparison with differential forms is assumed.
-/

open _root_.CategoryTheory Opposite _root_.TopologicalSpace

variable {R : Type} [Ring R]

/-- Singular cochain complexes on the open subsets of a topological space. -/
def singularCochainPresheaf (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    X.Presheaf (CochainComplex (ModuleCat.{0} R) ℕ) :=
  (Opens.toTopCat X).op ⋙ Cohomology.Singular.Functor.singularCochainsFunctor M

/-- The degree-`n` singular cochain presheaf, with genuine subspace topology. -/
def singularCochainDegreePresheaf (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    X.Presheaf (ModuleCat.{0} R) :=
  singularCochainPresheaf M X ⋙
    HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.up ℕ) n

/-- The presheaf assigning singular cohomology to each open subset. -/
def singularCohomologyPresheaf (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    X.Presheaf (ModuleCat.{0} R) :=
  (Opens.toTopCat X).op ⋙ Cohomology.Singular.Functor.singularCohomologyFunctor M n

@[simp]
theorem singularCochainPresheaf_obj (M : ModuleCat.{0} R) (X : TopCat.{0})
    (U : Opens X) :
    (singularCochainPresheaf M X).obj (op U) =
      Cohomology.Singular.Basic.singularCochains M (TopCat.of U) := rfl

/-- Restriction is pullback along the actual continuous inclusion of open sets. -/
@[simp]
theorem singularCochainPresheaf_map (M : ModuleCat.{0} R) (X : TopCat.{0})
    {U V : Opens X} (i : U ⟶ V) :
    (singularCochainPresheaf M X).map i.op =
      Cohomology.Singular.Functor.singularPullback M ((Opens.toTopCat X).map i) := rfl

@[simp]
theorem singularCochainDegreePresheaf_obj (M : ModuleCat.{0} R) (X : TopCat.{0})
    (U : Opens X) (n : ℕ) :
    (singularCochainDegreePresheaf M X n).obj (op U) =
      (Cohomology.Singular.Basic.singularCochains M (TopCat.of U)).X n := rfl

@[simp]
theorem singularCohomologyPresheaf_obj (M : ModuleCat.{0} R) (X : TopCat.{0})
    (U : Opens X) (n : ℕ) :
    (singularCohomologyPresheaf M X n).obj (op U) =
      Cohomology.Singular.Basic.singularCohomology M (TopCat.of U) n := rfl

/-- The presheaf differential is the ordinary singular coboundary on each open set. -/
def singularPresheafComplex (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{0} R) ℕ where
  X := singularCochainDegreePresheaf M X
  d i j :=
    { app := fun U => ((singularCochainPresheaf M X).obj U).d i j
      naturality := fun U V f => ((singularCochainPresheaf M X).map f).comm i j }
  shape i j h := by
    apply NatTrans.ext
    funext U
    exact ((singularCochainPresheaf M X).obj U).shape i j h
  d_comp_d' i j k _ _ := by
    apply NatTrans.ext
    funext U
    exact ((singularCochainPresheaf M X).obj U).d_comp_d i j k

@[simp]
theorem singularPresheafComplex_d_app (M : ModuleCat.{0} R) (X : TopCat.{0})
    (U : Opens X) (i j : ℕ) :
    ((singularPresheafComplex M X).d i j).app (op U) =
      (Cohomology.Singular.Basic.singularCochains M (TopCat.of U)).d i j := rfl

/-- The top open subset recovers the cochains of the original topological space. -/
def singularCochainPresheafTopIso (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    (singularCochainPresheaf M X).obj (op ⊤) ≅ Cohomology.Singular.Basic.singularCochains M X :=
  (Cohomology.Singular.Functor.singularCochainsFunctor M).mapIso (Opens.inclusionTopIso X).op.symm

/-- The top open subset recovers ordinary singular cohomology. -/
def singularCohomologyPresheafTopIso (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    (singularCohomologyPresheaf M X n).obj (op ⊤) ≅
      Cohomology.Singular.Basic.singularCohomology M X n :=
  (Cohomology.Singular.Functor.singularCohomologyFunctor M n).mapIso (Opens.inclusionTopIso X).op.symm

end

end OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf
