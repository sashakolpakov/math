import OAI.AlgebraicGeometry.ComplexMultiplication.GeometricMonomialReduction
import OAI.AlgebraicGeometry.ComplexMultiplication.CM.LineTransfer
import OAI.AlgebraicGeometry.ComplexMultiplication.RealizedHodgeMaps

/-! # Balanced Monomials -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.BalancedMonomials

noncomputable section

/-!
# BalancedMonomials: conditional reduction to balanced embedding monomials

The conclusion below is the full conjunction in Statements/BalancedMonomials.lean.
The supplied RiemannProjectivity proposition is specialized to the common coefficient field;
DegreeTwo is used only in its weight-one form. These replace the statement's broader
Riemann-realization and rational-fullness hypotheses, respectively.

ExteriorCohomology is already supplied by the target's chosen AbelianExteriorComparison C.
The scalar-descent/line-transfer lemmas used here have existing proofs, so a
separate ScalarDescent hypothesis is unnecessary. Kunneth, LineBundleCycles, ThomClass and the other parts of
DegreeTwo are unnecessary for the committed formulation: it states algebraic H¹
pullback-span membership, not an additional product/Künneth cycle construction.
Balanced-monomial algebraicity remains the antecedent of the reduction, exactly
as in the specification. No statement stub is imported or used.
-/

open scoped TensorProduct Classical
open _root_.CategoryTheory
open OAI.AlgebraicGeometry.ComplexMultiplication.CM.LineTransfer

/-- The supplied RiemannProjectivity statement at the coefficient field in question. -/
def CMRealizationInput (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E] : Prop :=
  ∀ (v : Gal(E/ℚ) → Bool)
    (hv : ∀ τ, v (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) = !(v τ)),
    Nonempty (ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E ⟨v, hv⟩))

/-- The weight-one proposition supplied by DegreeTwo, with its positive denominator. -/
def WeightOneAlgebraicityInput : Prop :=
  ∀ (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (u : A.variety.rationalCohomology 1 →ₗ[ℚ]
      B.variety.rationalCohomology 1),
    (∀ x ∈ A.h1Holomorphic, u.baseChange ℂ x ∈ B.h1Holomorphic) →
    (∀ x ∈ A.h1Antiholomorphic, u.baseChange ℂ x ∈ B.h1Antiholomorphic) →
    ∃ n : ℕ, 0 < n ∧ ∃ g : B.toOver ⟶ A.toOver,
      IsMonHom g ∧ ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback g = (n : ℚ) • u

/-- Clear the positive denominator in the supplied weight-one statement. -/
theorem fullness_of_DegreeTwo (hDegreeTwo : WeightOneAlgebraicityInput) :
    ComplexMultiplication.KnownAlgebraicity.CM.KnownResults.RationalH1MapsAreAlgebraic := by
  intro A B u hu10 hu01
  obtain ⟨n, hn, g, hg, heq⟩ := hDegreeTwo A B u hu10 hu01
  refine ⟨(n : ℚ)⁻¹, g, hg, ?_⟩
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [heq, smul_smul, inv_mul_cancel₀ hnq, one_smul]

/-- Change source coordinates in a scalar span of rational Hodge maps. -/
theorem precompose_realization_mem_hodge_span
    {U V : Type*} [AddCommGroup U] [Module ℚ U]
    [AddCommGroup V] [Module ℚ V]
    {J : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U} {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V}
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization J)
    (f : ComplexMultiplication.WeightOne.CM.Complexification U →ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification V)
    (hf : f ∈ ComplexMultiplication.Hodge.MapDescent.CM.rationalHodgeMapSpan J H) :
    f.comp (R.comparison.symm.toLinearMap.baseChange ℂ) ∈
      ComplexMultiplication.Hodge.MapDescent.CM.rationalHodgeMapSpan R.h1HodgeStructure H := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨q, hq, rfl⟩ := hf
      rw [← LinearMap.baseChange_comp]
      exact Submodule.subset_span
        ⟨q.comp R.comparison.symm.toLinearMap,
          hq.comp (J.transport_symm_isHodgeMap R.comparison), rfl⟩
  | zero =>
      simpa only [LinearMap.zero_comp] using
        (ComplexMultiplication.Hodge.MapDescent.CM.rationalHodgeMapSpan R.h1HodgeStructure H).zero_mem
  | add f g _ _ hf hg =>
      simpa only [LinearMap.add_comp] using
        (ComplexMultiplication.Hodge.MapDescent.CM.rationalHodgeMapSpan R.h1HodgeStructure H).add_mem hf hg
  | smul a f _ hf =>
      simpa only [LinearMap.smul_comp] using
        (ComplexMultiplication.Hodge.MapDescent.CM.rationalHodgeMapSpan R.h1HodgeStructure H).smul_mem a hf

variable {A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
  {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1)}

local instance (D : ComplexMultiplication.Decomposition.CM.CMDecomposition H) : LinearOrder D.EmbeddingIndex :=
  linearOrderOfSTO WellOrderingRel

/-- The committed BalancedMonomials conclusion, conditional on the supplied realization
and weight-one algebraicity inputs and the target's exterior comparison. -/
theorem reduction_to_balanced_embedding_monomials
    (D : ComplexMultiplication.Decomposition.CM.CMDecomposition H)
    (C : ComplexMultiplication.KnownExteriorCohomology.CM.AbelianExteriorComparison A H)
    (hhol : H.holomorphic = A.h1Holomorphic)
    (hanti : H.antiholomorphic = A.h1Antiholomorphic)
    (hRiemannProjectivity : CMRealizationInput D.commonCoefficientField)
    (hDegreeTwo : WeightOneAlgebraicityInput)
    (p : ℕ) :
    (∀ (a : A.variety.rationalCohomology (p + p)),
      a ∈ A.variety.rationalHodgeClasses p →
      ∀ s : D.ExteriorIndex (p + p),
        (D.exteriorEmbeddingBasis (p + p)).repr
          ((1 : D.commonCoefficientField) ⊗ₜ[ℚ]
            (C.rational (p + p)).symm a) s ≠ 0 →
        ∀ g : Gal(D.commonCoefficientField/ℚ),
          D.exteriorSignSum (p + p) s g = 0) ∧
    (∀ j : D.EmbeddingIndex,
      ∃ R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (D.embeddingLineSource j),
        D.embeddingLineTransfer j ∈
          ComplexMultiplication.Hodge.MapDescent.CM.rationalHodgeMapSpan (D.embeddingLineSource j) H ∧
        (D.embeddingLineTransfer j).comp
            (R.comparison.symm.toLinearMap.baseChange ℂ) ∈
          R.abelianVariety.algebraicH1PullbackSpan A) ∧
    ((∀ s : D.ExteriorIndex (p + p),
        (∀ g : Gal(D.commonCoefficientField/ℚ),
          D.exteriorSignSum (p + p) s g = 0) →
        C.complexMap (p + p)
            (D.complexExteriorEmbeddingBasis (p + p) s) ∈
          A.variety.complexGeometricAlgebraicClasses p) →
      A.variety.rationalHodgeClasses p ≤
        A.variety.geometricAlgebraicClasses p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha s hs g
    have htype := C.rational_hodge_preimage p a ha
    rw [D.exteriorPureSubspace_self_eq_balanced] at htype
    exact D.rational_exterior_support_balanced (p + p)
      ((C.rational (p + p)).symm a) htype s hs g
  · intro j
    obtain ⟨R⟩ := hRiemannProjectivity (D.galoisOddSign j).val (D.galoisOddSign j).property
    have hspan := D.embeddingLineTransfer_mem_rationalHodgeMapSpan j
    refine ⟨R, hspan, ?_⟩
    apply ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.rationalHodgeMapSpan_le_algebraicH1PullbackSpan
      (fullness_of_DegreeTwo hDegreeTwo) R.abelianVariety A R.h1HodgeStructure H
      R.h1HodgeStructure_holomorphic R.h1HodgeStructure_antiholomorphic hhol hanti
    exact precompose_realization_mem_hodge_span R (D.embeddingLineTransfer j) hspan
  · intro hmonomial a ha
    exact C.rational_hodge_mem_geometric_of_monomials D p hmonomial a ha

end

end OAI.AlgebraicGeometry.HodgeConjecture.BalancedMonomials
