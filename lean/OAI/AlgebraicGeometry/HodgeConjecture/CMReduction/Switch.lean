import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Definitions
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.Products

/-! # Switch -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Switch.CM.Construction

noncomputable section

/-!
The CycleCoefficients input is the full committed proposition, copied as a proposition
definition. The statement import supplies only CMReduction's switch definition;
its unproved theorem is never used. Product existence is constructed using
native scheme products, rather than supplied as a new assumption.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

def CycleCoefficientsInput : Prop :=
  ∀ (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v : Fin 4 →
      ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (_hbalance : ∀ τ : Gal(E/ℚ),
      ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val τ) =
        ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val τ))
    (A : Fin 4 → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : ∀ i, E ≃ₗ[ℚ] (A i).variety.rationalCohomology 1)
    (_hhol : ∀ i,
      ((ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)).holomorphic).map
          ((e i).toLinearMap.baseChange ℂ) = (A i).h1Holomorphic)
    (_hanti : ∀ i,
      ((ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)).antiholomorphic).map
          ((e i).toLinearMap.baseChange ℂ) = (A i).h1Antiholomorphic)
    (P : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (π : ∀ i, P.toOver ⟶ (A i).toOver)
    (_hproduct : IsLimit (Fan.mk P.toOver π)),
    let labels : Fin 4 → Gal(E/ℚ) :=
      fun i => if i.val < 2 then 1 else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E
    let x : Fin 4 → P.variety.complexCohomology 1 :=
      fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π i)
        ((A i).h1ScalarExtension ((e i).toLinearMap.baseChange ℂ
          (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E (labels i)))))
    let ξ : P.variety.complexCohomology 4 :=
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace P.toOver) 2 2
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ)
          (Betti.Scheme.schemePointSpace P.toOver) 1 1 (x 0) (x 1))
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ)
          (Betti.Scheme.schemePointSpace P.toOver) 1 1 (x 2) (x 3))
    ξ ≠ 0 ∧
      Submodule.span ℂ ({ξ} : Set (P.variety.complexCohomology 4)) ≤
        P.variety.complexGeometricAlgebraicClasses 2

theorem map_submodule_of_comparison
    {U V : Type*} [AddCommGroup U] [Module ℚ U]
    [AddCommGroup V] [Module ℚ V]
    (e : U ≃ₗ[ℚ] V)
    (S : Submodule ℂ (ComplexMultiplication.WeightOne.CM.Complexification U))
    (T : Submodule ℂ (ComplexMultiplication.WeightOne.CM.Complexification V))
    (h : ∀ x, e.toLinearMap.baseChange ℂ x ∈ T ↔ x ∈ S) :
    S.map (e.toLinearMap.baseChange ℂ) = T := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).mpr hx
  · intro hy
    obtain ⟨x, rfl⟩ := (e.baseChange ℚ ℂ U V).surjective y
    exact ⟨x, (h x).mp hy, rfl⟩

/-- The supplied CycleCoefficients proposition gives the exact switch premise of CMReduction. -/
theorem fourFactorSwitchAlgebraicity_of_CycleCoefficients (h_CycleCoefficients : CycleCoefficientsInput)
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E] :
    Definitions.CM.FourFactorSwitchAlgebraicity E := by
  intro v hv R
  let A : Fin 4 → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety := fun i => (R i).abelianVariety
  let B := CMVariety.Products.CM.Abelian.fourProduct A
  refine ⟨B, CMVariety.Products.CM.Abelian.fourProjection A, ⟨CMVariety.Products.CM.Abelian.fourProductIsLimit A⟩, ?_⟩
  have hhol : ∀ i,
      ((ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)).holomorphic).map
        ((R i).comparison.toLinearMap.baseChange ℂ) = (A i).h1Holomorphic :=
    fun i => map_submodule_of_comparison (R i).comparison _ _ (R i).holomorphic
  have hanti : ∀ i,
      ((ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)).antiholomorphic).map
        ((R i).comparison.toLinearMap.baseChange ℂ) = (A i).h1Antiholomorphic :=
    fun i => map_submodule_of_comparison (R i).comparison _ _ (R i).antiholomorphic
  have h := h_CycleCoefficients E v hv A (fun i => (R i).comparison) hhol hanti
    B (CMVariety.Products.CM.Abelian.fourProjection A) (CMVariety.Products.CM.Abelian.fourProductIsLimit A)
  exact h.2 (Submodule.subset_span (Set.mem_singleton _))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Switch.CM.Construction
