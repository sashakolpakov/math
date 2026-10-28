import OAI.Geometry.ComplexTorus.RiemannProjectivity.IntrinsicPureComparison
import OAI.AlgebraicGeometry.ComplexMultiplication.CMKnownResults

/-! # Intrinsic Comparison -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.IntrinsicComparison.Constructions

noncomputable section

section

/-! # RiemannProjectivity: the genuine rational H¹ comparison on the algebraic period model -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff TensorProduct
open OAI.AlgebraicGeometry.ComplexMultiplication.CMKnownResults.CM

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

def rationalComparison
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E), 𝓘(ℂ, V.analyticModel)⟯ V.analyticSpace) :
    E ≃ₗ[ℚ] V.rationalCohomology 1 :=
  (ComparisonField.Constructions.FieldComparison.fieldBettiEquiv Φ).trans (BettiTransportTop.Constructions.BettiTransport.iso ℚ e.toHomeomorph 1).toLinearEquiv.symm

theorem rational_pullback
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E), 𝓘(ℂ, V.analyticModel)⟯ V.analyticSpace) (a : E) :
    (BettiTransportTop.Constructions.BettiTransport.iso ℚ e.toHomeomorph 1).hom (rationalComparison Φ V e a) =
      ComparisonField.Constructions.FieldComparison.fieldBettiEquiv Φ a :=
  (BettiTransportTop.Constructions.BettiTransport.iso ℚ e.toHomeomorph 1).toLinearEquiv.apply_symm_apply _

theorem complex_pullback
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E), 𝓘(ℂ, V.analyticModel)⟯ V.analyticSpace)
    (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification E) :
    (BettiTransportTop.Constructions.BettiTransport.iso ℂ e.toHomeomorph 1).hom
      (AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (TopCat.of V.analyticSpace) 1
        ((rationalComparison Φ V e).toLinearMap.baseChange ℂ x)) =
      AnalyticRealizationEq.Constructions.AnalyticRealization.complexComparison Φ x := by
  refine (BettiTransportTop.Constructions.BettiTransport.complexification_naturality e.toHomeomorph 1
    ((rationalComparison Φ V e).toLinearMap.baseChange ℂ x)).trans ?_
  change AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (TopCat.of Φ.periodTorus) 1
    (((BettiTransportTop.Constructions.BettiTransport.iso ℚ e.toHomeomorph 1).hom.hom.baseChange ℂ)
      ((rationalComparison Φ V e).toLinearMap.baseChange ℂ x)) =
    AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (TopCat.of Φ.periodTorus) 1
      ((ComparisonField.Constructions.FieldComparison.fieldBettiEquiv Φ).toLinearMap.baseChange ℂ x)
  congr 1
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add]
    exact (((BettiTransportTop.Constructions.BettiTransport.iso ℚ e.toHomeomorph 1).hom.hom.baseChange ℂ).map_add _ _).trans
      (congrArg₂ (· + ·) hx hy)
  | tmul c a =>
    simp only [LinearMap.baseChange_tmul]
    exact congrArg (fun y => c ⊗ₜ[ℚ] y) (rational_pullback Φ V e a)

theorem holomorphic
    (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E), 𝓘(ℂ, A.variety.analyticModel)⟯ A.variety.analyticSpace)
    (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification E) :
    (rationalComparison Φ A.variety e).toLinearMap.baseChange ℂ x ∈ A.h1Holomorphic ↔
      x ∈ Φ.hodgeStructure.holomorphic := by
  change A.h1ScalarExtension ((rationalComparison Φ A.variety e).toLinearMap.baseChange ℂ x) ∈
    A.variety.pureBettiSubspace 1 0 ↔ _
  rw [IntrinsicPureComparison.Constructions.pureBetti_iff Φ A.variety e 1 0]
  change (∃ a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1,
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1 0 a.val ∧
    BettiDe.Constructions.Betti.deRhamBettiEquiv Φ 1 (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1 a) =
      (BettiTransportTop.Constructions.BettiTransport.iso ℂ e.toHomeomorph 1).hom
        (AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (TopCat.of A.variety.analyticSpace) 1
          ((rationalComparison Φ A.variety e).toLinearMap.baseChange ℂ x))) ↔ _
  rw [complex_pullback]
  exact AnalyticRealizationEq.Constructions.AnalyticRealization.holomorphic_comparison Φ x

theorem antiholomorphic
    (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E), 𝓘(ℂ, A.variety.analyticModel)⟯ A.variety.analyticSpace)
    (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification E) :
    (rationalComparison Φ A.variety e).toLinearMap.baseChange ℂ x ∈ A.h1Antiholomorphic ↔
      x ∈ Φ.hodgeStructure.antiholomorphic := by
  change A.h1ScalarExtension ((rationalComparison Φ A.variety e).toLinearMap.baseChange ℂ x) ∈
    A.variety.pureBettiSubspace 0 1 ↔ _
  rw [IntrinsicPureComparison.Constructions.pureBetti_iff Φ A.variety e 0 1]
  change (∃ a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1,
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 0 1 a.val ∧
    BettiDe.Constructions.Betti.deRhamBettiEquiv Φ 1 (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1 a) =
      (BettiTransportTop.Constructions.BettiTransport.iso ℂ e.toHomeomorph 1).hom
        (AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (TopCat.of A.variety.analyticSpace) 1
          ((rationalComparison Φ A.variety e).toLinearMap.baseChange ℂ x))) ↔ _
  rw [complex_pullback]
  exact AnalyticRealizationEq.Constructions.AnalyticRealization.antiholomorphic_comparison Φ x

end

/-! # RiemannProjectivity: realization in actual abelian-variety rational H¹ -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff
open OAI.AlgebraicGeometry.ComplexMultiplication.CMKnownResults.CM

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]

theorem realization_of_embedding_type (hRiemannProjectivity : Fin.Constructions.RiemannProjectivityInput) (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    Nonempty (AlgebraicGeometry.ComplexMultiplication.CMKnownResults.CM.HodgeRealization Φ.hodgeStructure) := by
  obtain ⟨A, ⟨e⟩⟩ := AbelianModel.Constructions.AbelianTorusModel.exists_abelian_model hRiemannProjectivity Φ
  let e' : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E), 𝓘(ℂ, A.variety.analyticModel)⟯ A.variety.analyticSpace := e
  exact ⟨{
    abelianVariety := A
    comparison := rationalComparison Φ A.variety e'
    holomorphic := Constructions.holomorphic Φ A e'
    antiholomorphic := Constructions.antiholomorphic Φ A e'
  }⟩

theorem realization_of_cm_sign_type (hRiemannProjectivity : Fin.Constructions.RiemannProjectivityInput)
    (K : IntermediateField ℚ ℂ) [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
    (v : Gal(K/ℚ) → Bool) (hv : ∀ τ : Gal(K/ℚ), v (AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * τ) = !(v τ)) :
    Nonempty (AlgebraicGeometry.ComplexMultiplication.CMKnownResults.CM.HodgeRealization (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure K ⟨v, hv⟩)) :=
  realization_of_embedding_type hRiemannProjectivity (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.embeddingType K ⟨v, hv⟩)

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.IntrinsicComparison.Constructions
