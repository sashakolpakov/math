import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.Products
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Definitions
import OAI.AlgebraicGeometry.ComplexMultiplication.CM.KnownRealization

/-! # Switch Of -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.SwitchOf.CM.Abelian

noncomputable section

/-!
The SurfaceConstruction input below is its committed statement, with the theorem proof
replaced by a proposition definition. The proof uses only a named hypothesis
of that type. The CMReduction import supplies `FourFactorSwitchAlgebraicity`; its
unproved reduction theorem is never used as a fact.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

/-- Exact proposition specified by the committed SurfaceConstruction declaration. -/
def SwitchCycleInput : Prop :=
  ∀ (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v : Fin 4 →
      ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
        (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (_hswitch : ∀ τ : Gal(E/ℚ),
      ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val τ) =
        ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val τ))
    (R : ∀ i : Fin 4,
      ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : ∀ i : Fin 4, X.toOver ⟶ (R i).abelianVariety.toOver)
    (_hproduct : IsLimit (Fan.mk X.toOver π)),
    let u : Fin 4 → Gal(E/ℚ) → X.complexCohomology 1 :=
      fun i τ =>
        Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π i)
          ((R i).complexComparison
            (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E
              (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ)))
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
          (a j : ℂ) •
            X.rationalCohomologyInclusion 4
              (X.geometricCycleClassMap 2 (Z j))) = t

/-- A rational geometric cycle remains algebraic after extending coefficients. -/
theorem cycleClass_mem_complexAlgebraic
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    (Z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle X p) :
    X.rationalCohomologyInclusion (p + p) (X.geometricCycleClassMap p Z) ∈
      X.complexGeometricAlgebraicClasses p := by
  have hmem :
      ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) (p + p)
        ((1 : ℂ) ⊗ₜ[ℚ] (X.geometricCycleClassMap p Z)) ∈
          X.complexGeometricAlgebraicClasses p :=
    Submodule.mem_map.mpr
      ⟨(1 : ℂ) ⊗ₜ[ℚ] (X.geometricCycleClassMap p Z),
        Submodule.tmul_mem_baseChange_of_mem 1 ⟨Z, rfl⟩, rfl⟩
  simpa only [ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul, one_smul] using! hmem

/-- SurfaceConstruction supplies CMReduction's switch premise on an actual fourfold abelian product. -/
theorem fourFactorSwitchAlgebraicity_of_SurfaceConstruction (hSurfaceConstruction : SwitchCycleInput)
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E] :
    CMReduction.Definitions.CM.FourFactorSwitchAlgebraicity E := by
  intro v hv R
  let A : Fin 4 → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety := fun i => (R i).abelianVariety
  let B := Products.CM.Abelian.fourProduct A
  refine ⟨B, Products.CM.Abelian.fourProjection A, ⟨Products.CM.Abelian.fourProductIsLimit A⟩, ?_⟩
  obtain ⟨n, a, Z, hZ⟩ :=
    (hSurfaceConstruction E v hv R B.variety (Products.CM.Abelian.fourProjection A) (Products.CM.Abelian.fourProductIsLimit A)).2
  have hmem :
      (∑ j : Fin n, (a j : ℂ) •
        B.variety.rationalCohomologyInclusion 4
          (B.variety.geometricCycleClassMap 2 (Z j))) ∈
        B.variety.complexGeometricAlgebraicClasses 2 := by
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (cycleClass_mem_complexAlgebraic B.variety 2 (Z j))
  rw [hZ] at hmem
  simpa [ComplexMultiplication.CMKnownResults.CM.HodgeRealization.complexComparison_apply] using! hmem

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.SwitchOf.CM.Abelian
