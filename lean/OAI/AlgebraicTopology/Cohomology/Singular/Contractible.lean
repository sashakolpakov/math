import OAI.AlgebraicTopology.Cohomology.Singular.Homotopy
import OAI.AlgebraicTopology.Cohomology.Singular.Representatives
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Convex

/-! # Contractible -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.Contractible

noncomputable section

/-!
# Positive-degree singular cohomology of contractible spaces

These are statements about the genuine singular cochain complex. The proof
uses mathlib's computation for totally disconnected spaces, followed by the
proved invariance under continuous homotopy equivalences. Contractibility is
mathlib's actual homotopy equivalence to a one-point space.

For positive-degree cocycles this gives an actual lower-degree singular
cochain whose coboundary is the original cocycle. Convex and star-convex
specializations use the existing continuous straight-line contractions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

variable {R : Type} [Ring R]

/-- Positive-degree singular cohomology vanishes for totally disconnected
spaces, by the corresponding general homology computation in the opposite
category of modules. -/
theorem isZero_singularCohomology_of_totallyDisconnected (M : ModuleCat.{0} R)
    (X : TopCat.{0}) [TotallyDisconnectedSpace X] (n : ℕ) (hn : n ≠ 0) :
    IsZero (Basic.singularCohomology M X n) := by
  have h := AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat.{0} R)ᵒᵖ n (op M) X hn
  exact h.unop.of_iso (Basic.singularCohomologyOppositeIso M X n)

/-- An actual homotopy equivalence to the one-point space implies vanishing
of positive-degree singular cohomology. -/
theorem isZero_singularCohomology_of_homotopyEquiv_unit (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (e : ContinuousMap.HomotopyEquiv X Unit)
    (n : ℕ) (hn : n ≠ 0) : IsZero (Basic.singularCohomology M X n) :=
  (isZero_singularCohomology_of_totallyDisconnected M (TopCat.of Unit) n hn).of_iso
    (Homotopy.singularCohomologyIsoOfHomotopyEquiv M (Y := TopCat.of Unit) e n).symm

/-- Positive-degree singular cohomology vanishes on every contractible space. -/
theorem isZero_singularCohomology_of_contractible (M : ModuleCat.{0} R)
    (X : TopCat.{0}) [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    IsZero (Basic.singularCohomology M X n) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  exact isZero_singularCohomology_of_homotopyEquiv_unit M X e n hn

/-- Elementwise version of contractible-space vanishing. -/
theorem singularCohomology_eq_zero_of_contractible (M : ModuleCat.{0} R)
    (X : TopCat.{0}) [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0)
    (c : Basic.singularCohomology M X n) : c = 0 := by
  let := ModuleCat.subsingleton_of_isZero
    (isZero_singularCohomology_of_contractible M X n hn)
  exact Subsingleton.elim c 0

/-- The genuine singular cochain complex of a contractible space is exact
in every positive degree. -/
theorem singularCochains_exactAt_of_contractible (M : ModuleCat.{0} R)
    (X : TopCat.{0}) [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    (Basic.singularCochains M X).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact isZero_singularCohomology_of_contractible M X n hn

/-- Every positive-degree singular cocycle on a contractible space admits a
singular cochain primitive. -/
theorem exists_singularPrimitive_of_contractible (M : ModuleCat.{0} R)
    (X : TopCat.{0}) [ContractibleSpace X] (n : ℕ)
    (c : Representatives.singularCocycles M X (n + 1)) :
    ∃ b : (Basic.singularCochains M X).X n,
      ((Basic.singularCochains M X).d n (n + 1)) b = c.1 := by
  have h : Representatives.singularClass M X (n + 1) c = Representatives.singularClass M X (n + 1) 0 := by
    rw [map_zero]
    exact singularCohomology_eq_zero_of_contractible M X (n + 1) (Nat.succ_ne_zero n) _
  simpa using (Representatives.singularClass_eq_iff_exists_succ M X n c 0).mp h

section RealTopologicalVectorSpace

variable {E : Type} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul ℝ E]

/-- Positive-degree singular cohomology vanishes on nonempty star-convex sets. -/
theorem isZero_singularCohomology_of_starConvex (M : ModuleCat.{0} R)
    {s : Set E} {x : E} (hs : StarConvex ℝ x s) (hne : s.Nonempty)
    (n : ℕ) (hn : n ≠ 0) : IsZero (Basic.singularCohomology M (TopCat.of s) n) := by
  let : ContractibleSpace s := hs.contractibleSpace hne
  exact isZero_singularCohomology_of_contractible M (TopCat.of s) n hn

/-- Positive-degree singular cohomology vanishes on nonempty convex sets. -/
theorem isZero_singularCohomology_of_convex (M : ModuleCat.{0} R)
    {s : Set E} (hs : Convex ℝ s) (hne : s.Nonempty)
    (n : ℕ) (hn : n ≠ 0) : IsZero (Basic.singularCohomology M (TopCat.of s) n) := by
  let : ContractibleSpace s := hs.contractibleSpace hne
  exact isZero_singularCohomology_of_contractible M (TopCat.of s) n hn

/-- Singular cocycles of positive degree on a nonempty convex set have
singular cochain primitives. -/
theorem exists_singularPrimitive_of_convex (M : ModuleCat.{0} R)
    {s : Set E} (hs : Convex ℝ s) (hne : s.Nonempty) (n : ℕ)
    (c : Representatives.singularCocycles M (TopCat.of s) (n + 1)) :
    ∃ b : (Basic.singularCochains M (TopCat.of s)).X n,
      ((Basic.singularCochains M (TopCat.of s)).d n (n + 1)) b = c.1 := by
  let : ContractibleSpace s := hs.contractibleSpace hne
  exact exists_singularPrimitive_of_contractible M (TopCat.of s) n c

end RealTopologicalVectorSpace

/-- In particular, every positive-radius open ball in a real normed vector
space has vanishing singular cohomology in positive degrees. -/
theorem isZero_singularCohomology_ball (M : ModuleCat.{0} R)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (r : ℝ) (hr : 0 < r) (n : ℕ) (hn : n ≠ 0) :
    IsZero (Basic.singularCohomology M (TopCat.of (Metric.ball x r)) n) :=
  isZero_singularCohomology_of_convex M (convex_ball x r)
    ⟨x, Metric.mem_ball_self hr⟩ n hn

end

end OAI.AlgebraicTopology.Cohomology.Singular.Contractible
