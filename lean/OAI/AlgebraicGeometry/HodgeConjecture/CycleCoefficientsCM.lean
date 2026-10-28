import OAI.AlgebraicGeometry.ComplexMultiplication.CM.KnownRealization
import OAI.AlgebraicGeometry.ComplexMultiplication.ClassDescent
import OAI.AlgebraicTopology.Products.CupCohomology
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Cycle Coefficients CM -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CycleCoefficientsCM.CM.Construction

noncomputable section

/-!
# CycleCoefficients conditional on the committed SurfaceConstruction specification

`SurfaceConstructionInput` repeats the supplied proposition without importing its statement
stub. The proof packages the given Hodge realizations, then places the finite
E-linear cycle combination in the complex span of genuine rational cycle
classes. All original target hypotheses are retained. No additional substantive
assumption is used; the auxiliary surface construction belongs to SurfaceConstruction.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct
open OAI.AlgebraicGeometry.ComplexMultiplication.CM.KnownRealization.CMCoefficientField

/-- The full committed SurfaceConstruction proposition, used only as an explicit input. -/
def SurfaceConstructionInput : Prop :=
  ∀ (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v : Fin 4 →
      ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (_hswitch : ∀ τ : Gal(E/ℚ),
      ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val τ) =
        ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val τ))
    (R : ∀ i : Fin 4, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : ∀ i : Fin 4, X.toOver ⟶ (R i).abelianVariety.toOver)
    (_hproduct : IsLimit (Fan.mk X.toOver π)),
    let u : Fin 4 → Gal(E/ℚ) → X.complexCohomology 1 :=
      fun i τ =>
        Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π i)
          ((R i).complexComparison
            (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ)))
    let c := ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E
    let t : X.complexCohomology 4 :=
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ)
        (Betti.Scheme.schemePointSpace X.toOver) 2 2
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ)
          (Betti.Scheme.schemePointSpace X.toOver) 1 1 (u 0 1) (u 1 1))
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ)
          (Betti.Scheme.schemePointSpace X.toOver) 1 1 (u 2 c) (u 3 c))
    t ≠ 0 ∧
      ∃ (n : ℕ) (a : Fin n → E)
        (Z : Fin n → CycleClass.Geometric.DimensionCycles.RationalDimensionCycle X 2),
        (∑ j : Fin n,
          (a j : ℂ) • X.rationalCohomologyInclusion 4
            (X.geometricCycleClassMap 2 (Z j))) = t

/-- An image equality under a rational isomorphism gives the pointwise
Hodge-type comparison required by `HodgeRealization`. -/
private theorem type_comparison
    {U V : Type*} [AddCommGroup U] [Module ℚ U]
    [AddCommGroup V] [Module ℚ V]
    (e : U ≃ₗ[ℚ] V)
    (S : Submodule ℂ (ComplexMultiplication.WeightOne.CM.Complexification U))
    (T : Submodule ℂ (ComplexMultiplication.WeightOne.CM.Complexification V))
    (h : S.map (e.toLinearMap.baseChange ℂ) = T)
    (x : ComplexMultiplication.WeightOne.CM.Complexification U) :
    e.toLinearMap.baseChange ℂ x ∈ T ↔ x ∈ S := by
  rw [← h]
  constructor
  · rintro ⟨y, hy, heq⟩
    have hxy : y = x := (e.baseChange ℚ ℂ U V).injective heq
    exact hxy ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- A genuine rational cycle class belongs to its complex cycle-class span. -/
private theorem cycle_mem_complex_span
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    (Z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle X p) :
    X.rationalCohomologyInclusion (p + p)
      (X.geometricCycleClassMap p Z) ∈
        X.complexGeometricAlgebraicClasses p := by
  change ∃ w : ComplexMultiplication.WeightOne.CM.Complexification (X.rationalCohomology (p + p)),
    w ∈ (X.geometricAlgebraicClasses p).baseChange ℂ ∧
      ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) (p + p) w = _
  refine ⟨(1 : ℂ) ⊗ₜ[ℚ] (X.geometricCycleClassMap p Z), ?_, ?_⟩
  · exact Submodule.tmul_mem_baseChange_of_mem 1 ⟨Z, rfl⟩
  · exact (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul
      (Betti.Scheme.schemePointSpace X.toOver) (p + p) 1 (X.geometricCycleClassMap p Z)).trans
        (one_smul ℂ _)

/-- CycleCoefficients, with exactly the original natural hypotheses and explicit SurfaceConstruction input. -/
theorem four_factor_switch_algebraic
    (h_SurfaceConstruction : SurfaceConstructionInput)
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v : Fin 4 →
      ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (hbalance : ∀ τ : Gal(E/ℚ),
      ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val τ) =
        ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val τ))
    (A : Fin 4 → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : ∀ i, E ≃ₗ[ℚ] (A i).variety.rationalCohomology 1)
    (hhol : ∀ i,
      ((ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)).holomorphic).map
          ((e i).toLinearMap.baseChange ℂ) = (A i).h1Holomorphic)
    (hanti : ∀ i,
      ((ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)).antiholomorphic).map
          ((e i).toLinearMap.baseChange ℂ) = (A i).h1Antiholomorphic)
    (P : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (π : ∀ i, P.toOver ⟶ (A i).toOver)
    (hproduct : IsLimit (Fan.mk P.toOver π)) :
    let labels : Fin 4 → Gal(E/ℚ) :=
      fun i => if i.val < 2 then 1 else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E
    let x : Fin 4 → P.variety.complexCohomology 1 :=
      fun i =>
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π i))
          ((A i).h1ScalarExtension
            ((e i).toLinearMap.baseChange ℂ
              (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E (labels i)))))
    let ξ : P.variety.complexCohomology 4 :=
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup
        (R := ℂ) (Betti.Scheme.schemePointSpace P.toOver) 2 2
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup
          (R := ℂ) (Betti.Scheme.schemePointSpace P.toOver) 1 1 (x 0) (x 1))
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup
          (R := ℂ) (Betti.Scheme.schemePointSpace P.toOver) 1 1 (x 2) (x 3))
    ξ ≠ 0 ∧
      Submodule.span ℂ ({ξ} : Set (P.variety.complexCohomology 4)) ≤
        P.variety.complexGeometricAlgebraicClasses 2 := by
  let R : ∀ i : Fin 4, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)) :=
    fun i =>
      { abelianVariety := A i
        comparison := e i
        holomorphic := type_comparison (e i) _ _ (hhol i)
        antiholomorphic := type_comparison (e i) _ _ (hanti i) }
  obtain ⟨hne, n, a, Z, hZ⟩ := h_SurfaceConstruction E v hbalance R P.variety π hproduct
  refine ⟨hne, ?_⟩
  apply Submodule.span_le.mpr
  intro y hy
  obtain rfl := Set.mem_singleton_iff.mp hy
  suffices hsum : (∑ j : Fin n,
      (a j : ℂ) • P.variety.rationalCohomologyInclusion 4
        (P.variety.geometricCycleClassMap 2 (Z j))) ∈
      P.variety.complexGeometricAlgebraicClasses 2 by
    exact hZ ▸ hsum
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (cycle_mem_complex_span P.variety 2 (Z j))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CycleCoefficientsCM.CM.Construction
