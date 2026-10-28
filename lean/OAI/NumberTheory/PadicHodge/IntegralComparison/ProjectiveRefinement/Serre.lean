import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.PureDuality
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.DualMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.PureFunctorNaturality

/-! # Serre -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.Serre

noncomputable section

/-! Pure projective Serre pairings for the fixed negative resolution
and its literal common refinement. Purity of the fixed dual complex
passes to the common refinement through the original quasi-isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

variable (M N : (Proj (homogeneousSubmodule σ R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent] [N.IsFiniteType]
  (B n : ℕ) (hn : Fintype.card σ = n + 2) (hB : n + 2 ≤ B)

abbrev fixedTower := Projective.NegativeResolution.tower M (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B

omit [Module.Injective R R] in
theorem fixed_above (q : ℕ) :
    NegativeTerms.Above ((fixedTower M B n hn).term q) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B :=
  DualMap.fixed_term_above M (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B q

abbrev fixedDual := ProjectiveTower.PureDuality.dualComplex (fixedTower M B n hn) n hn

def cohomologyFunctor (i : ℕ) : (Proj (homogeneousSubmodule σ R)).Modules ⥤ AddCommGrpCat.{u} :=
  Trace.PureFunctorNaturality.cohomologyFunctor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) i

variable (c : ℕ) (hM : ∀ q, q ≠ c → (fixedDual M B n hn).ExactAt q)

def pairing (i : ℕ) (hi : i + c ≤ n + 1) :=
  ProjectiveTower.PureDuality.iso (fixedTower M B n hn) B n hn
    (fixed_above M B n hn) hB c hM i hi

variable (f : M ⟶ N)

omit [Module.Injective R R] in
include hB hM in
theorem common_exactAt (q : ℕ) (hq : q ≠ c) :
    (ProjectiveTower.PureDuality.dualComplex
      (Projective.NegativeRefinement.tower M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B f) n hn).ExactAt q := by
  let := DualMap.left_quasiIso M N
    (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B (n + 2) hB f
  exact (exactAt_iff_of_quasiIsoAt
    (DualMap.leftMap M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B (n + 2) f) q).mp
      (hM q hq)

def commonPairing (i : ℕ) (hi : i + c ≤ n + 1) :=
  ProjectiveTower.PureDuality.iso
    (Projective.NegativeRefinement.tower M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B f) B n hn
    (Projective.NegativeRefinement.term_above M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B f) hB c
    (common_exactAt M N B n hn hB c hM f) i hi

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.Serre
