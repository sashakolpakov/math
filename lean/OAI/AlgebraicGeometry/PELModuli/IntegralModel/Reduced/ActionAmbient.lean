import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.RosatiActionAmbient
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduction

/-! # Action Ambient -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ActionAmbient

noncomputable section

/-! Reduction of the actual bounded integral-action ambient preserves
its classification of Rosati actions on every reduced test scheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

instance reduction_locallyOfFiniteType {S : Scheme} (Z : Over S) [LocallyOfFiniteType Z.hom] :
    LocallyOfFiniteType (Reduction.reduction Z).hom := by
  change LocallyOfFiniteType ((Reduction.reductionι Z).left ≫ Z.hom)
  infer_instance

instance reduction_quasiCompact {S : Scheme} (Z : Over S) [QuasiCompact Z.hom] :
    QuasiCompact (Reduction.reduction Z).hom := by
  change QuasiCompact ((Reduction.reductionι Z).left ≫ Z.hom)
  infer_instance

instance reduction_separated {S : Scheme} (Z : Over S) [IsSeparated Z.hom] :
    IsSeparated (Reduction.reduction Z).hom := by
  change IsSeparated ((Reduction.reductionι Z).left ≫ Z.hom)
  infer_instance

theorem exists_reduced_bounded_action_ambient_for_rosati
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
    (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (hc : ∀ s : Spec (.of k), IsUnit (D.conductor : (Spec (.of k)).presheaf.stalk s)) :
    ∃ Z : Over (Spec (.of k)), IsReduced Z.left ∧ LocallyOfFiniteType Z.hom ∧
      QuasiCompact Z.hom ∧ IsSeparated Z.hom ∧
      ∃ ρZ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback Z.hom),
        ∀ (T : Over (Spec (.of k))) [IsReduced T.left]
          (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback T.hom)),
          AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback T.hom) ρ →
            ∃! f : T ⟶ Z, Integral.ActionScheme.restrictIntegralAction A.abelian ρZ f = ρ := by
  obtain ⟨Z, hft, hqc, hsep, ρZ, hclass⟩ :=
    Presentations.RosatiActionAmbient.exists_e34_bounded_action_ambient_for_rosati D A hPresentations hc
  let := hft
  let := hqc
  let := hsep
  refine ⟨Reduction.reduction Z, inferInstance, inferInstance, inferInstance, inferInstance,
    Integral.ActionScheme.restrictIntegralAction A.abelian ρZ (Reduction.reductionι Z), ?_⟩
  intro T hT ρ hρ
  obtain ⟨f, hf, huniq⟩ := hclass T ρ hρ
  refine ⟨Reduction.factorToReduction f, ?_, ?_⟩
  · change Integral.ActionScheme.restrictIntegralAction A.abelian
      (Integral.ActionScheme.restrictIntegralAction A.abelian ρZ (Reduction.reductionι Z)) (Reduction.factorToReduction f) = ρ
    rw [← Integral.ActionScheme.restrictIntegralAction_comp, Reduction.factorToReduction_ι]
    exact hf
  · intro q hq
    apply (cancel_mono (Reduction.reductionι Z)).mp
    rw [Reduction.factorToReduction_ι]
    apply huniq
    rw [Integral.ActionScheme.restrictIntegralAction_comp]
    exact hq

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ActionAmbient
