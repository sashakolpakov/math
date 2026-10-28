import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AbelianProjectivePresentation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Canonical
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Active
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BettiComparison
import OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.HeckeAction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Naturality

/-! # Comap -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Comap.CM

noncomputable section

/-! The original Albanese has a constructed projective presentation and
canonical weight-one Hodge structure. Every actual Hecke presentation
preserves its Hodge pieces by algebraic pullback naturality. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Canonical.CM

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]}
  (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq) (j : K →+* ℂ)

abbrev variety : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety :=
  (A.complexAbelianVariety j (AbelianProjectivePresentation.CM.presentation A j)).variety

def hodge : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.Betti j) := Canonical.CM.canonicalHodge (CM.variety A j)

theorem holomorphic_comap :
    (hodge A j).holomorphic =
      (A.bettiFiltration j (AbelianProjectivePresentation.CM.presentation A j) 1).comap
        (BettiComparison.CM.coefficientMap A j) := by
  change ((CM.variety A j).pureBettiSubspace 1 0).comap _ = _
  rw [← CMExtraction.Naturality.integral_presentation_pure (CM.variety A j)]
  rfl

theorem antiholomorphic_comap :
    (hodge A j).antiholomorphic =
      ((A.smoothProjectiveFiber j (AbelianProjectivePresentation.CM.presentation A j)).pureBettiSubspace 0 1).comap
        (BettiComparison.CM.coefficientMap A j) := by
  change ((CM.variety A j).pureBettiSubspace 0 1).comap _ = _
  rw [← CMExtraction.Naturality.integral_presentation_pure (CM.variety A j)]
  rfl

theorem pullback_hodge (f : A.ExtendingEndomorphism) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (hodge A j) (hodge A j) (A.bettiPullback j f) :=
  GeometricSource.CM.actual_restriction_isHodgeMap
    (X := CM.variety A j) (Y := CM.variety A j) (A.complexEndomorphism j f)
    (hodge A j) (hodge A j) rfl rfl

theorem hecke_hodge {H : Type} [CommRing H] [Algebra ℚ H]
    (ρ : A.HeckeRealization H) (h : H) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (hodge A j) (hodge A j) (A.bettiHecke j ρ h) := by
  apply (ComplexMultiplication.Hodge.MapDescent.CM.baseChange_mem_hodgeHomSubspace_iff (hodge A j) (hodge A j) _).mp
  change (Module.End.baseChangeHom ℚ ℂ (A.Betti j))
    ((ρ.presentation h).sum (fun f a => a • A.bettiPullback j f)) ∈ _
  simp only [Finsupp.sum, map_sum, map_smul]
  apply Submodule.sum_mem
  intro f _
  exact ((ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace (hodge A j) (hodge A j)).restrictScalars ℚ).smul_mem _
    ((ComplexMultiplication.Hodge.MapDescent.CM.baseChange_mem_hodgeHomSubspace_iff (hodge A j) (hodge A j) _).mpr
      (pullback_hodge A j f))

def heckeAction {H : Type} [CommRing H] [Algebra ℚ H]
    (ρ : A.HeckeRealization H) : H →ₐ[ℚ] Module.End ℚ (A.Betti j) :=
  A.bettiHeckeAction j (AbelianProjectivePresentation.CM.presentation A j) ρ

theorem heckeAction_apply {H : Type} [CommRing H] [Algebra ℚ H]
    (ρ : A.HeckeRealization H) (h : H) :
    heckeAction A j ρ h = A.bettiHecke j ρ h :=
  A.bettiHeckeAction_apply j (AbelianProjectivePresentation.CM.presentation A j) ρ h

theorem heckeAction_hodge {H : Type} [CommRing H] [Algebra ℚ H]
    (ρ : A.HeckeRealization H) (h : H) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (hodge A j) (hodge A j) (heckeAction A j ρ h) := by
  rw [heckeAction_apply]
  exact hecke_hodge A j ρ h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Comap.CM
