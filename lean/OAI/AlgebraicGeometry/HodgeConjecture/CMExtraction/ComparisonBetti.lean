import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Comparison
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Base

/-! # Comparison Betti -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ComparisonBetti

noncomputable section

/-! Canonical rational-to-complex coefficient extension intertwines the
actual GeometricComparison Hecke realization with the native active action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

section

theorem coefficientExtension_hecke
    {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
    {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)
    {H : Type} [CommRing H] [Algebra ℚ H]
    (j : K →+* ℂ) (R : A.HeckeRealization H) (h : H)
    (x : ComplexMultiplication.WeightOne.CM.Complexification (A.Betti j)) :
    ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (AlgebraicGeometry.Betti.Scheme.schemePointSpace (A.complexFiber j).scheme) 1
        ((A.bettiHecke j R h).baseChange ℂ x) =
      A.complexBettiHecke j R h
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (AlgebraicGeometry.Betti.Scheme.schemePointSpace (A.complexFiber j).scheme) 1 x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul z c =>
    simp only [LinearMap.baseChange_tmul, NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.bettiHecke,
      NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.complexBettiHecke, Finsupp.sum, LinearMap.sum_apply,
      LinearMap.smul_apply, TensorProduct.tmul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro f hf
    have hn := Naturality.complexification_pullback (A.complexEndomorphism j f) 1 (z ⊗ₜ[ℚ] c)
    simp only [LinearMap.baseChange_tmul] at hn
    change ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification _ 1
        (z ⊗ₜ[ℚ] ((R.presentation h) f • A.bettiPullback j f c)) =
      ((R.presentation h) f : ℂ) • A.complexBettiPullback j f
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification _ 1 (z ⊗ₜ[ℚ] c))
    rw [TensorProduct.tmul_smul, ← Rat.cast_smul_eq_qsmul ℂ, map_smul]
    exact congrArg (fun y => ((R.presentation h) f : ℂ) • y) hn

end

namespace Intrinsic

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def nativeBettiComplexification (hg : D.pel.HasIntegralModelGeometry) :
    ComplexMultiplication.WeightOne.CM.Complexification D.pel.H1 ≃ₗ[ℂ]
      AlgebraicGeometry.Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) D.pel.complexAlbanese.X 1 := by
  let : FiniteDimensional ℚ D.pel.H1 := Intrinsic.Base.native_betti_finite D hg
  exact ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexificationEquiv (AlgebraicGeometry.Betti.Scheme.schemePointSpace D.pel.complexAlbanese.X) 1

theorem native_comparison_intertwining
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
    (e : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ]
      RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q) :
    letI := Intrinsic.Comparison.nativeActiveCommRing D e hElementaryDivisors
    ∀ (R : (Intrinsic.Comparison.nativeComparisonModel D hg hq j).HeckeRealization (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q)),
      (Intrinsic.Comparison.nativeComparisonModel D hg hq j).bettiHecke D.pel.complexEmbedding R =
        (fun h => (Intrinsic.Forms.activeBettiAction D A e h : Module.End ℚ D.pel.H1)) →
      ∀ h x, nativeBettiComplexification D hg ((Intrinsic.Forms.activeBettiAction D A e h).baseChange ℂ x) =
        (Intrinsic.Comparison.nativeComparisonModel D hg hq j).complexBettiHecke D.pel.complexEmbedding R h
          (nativeBettiComplexification D hg x) := by
  let := Intrinsic.Comparison.nativeActiveCommRing D e hElementaryDivisors
  intro R hR h x
  have hc := coefficientExtension_hecke
    (Intrinsic.Comparison.nativeComparisonModel D hg hq j) D.pel.complexEmbedding R h x
  rw [congrFun hR h] at hc
  exact hc

end Intrinsic

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ComparisonBetti
