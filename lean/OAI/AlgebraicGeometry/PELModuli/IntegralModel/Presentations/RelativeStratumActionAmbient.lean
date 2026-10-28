import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.CMStratumGraphBound
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.ActionScheme
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ActionAmbient
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.ParameterPoints

/-! # Relative Stratum Action Ambient -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.RelativeStratumActionAmbient

noncomputable section

/-! The full corrected Presentations input constructs actual reduced finite-type
action parameters on each computed CM polynomial stratum of a varying
family. Every Rosati action on every reduced test in that stratum is
classified uniquely. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.ParameterPoints

theorem exists_e34_relative_stratum_action_ambient
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    {S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.abelian.scheme.left) (d : ℕ)
    (hP : AbelianModuli.HilbertConstruction.Tensor.Powers.IsTensorPower (Relative.PoincareSimilitude.RelativePoincareClasses.polarizationLine A.dual
      A.polarization.isogeny.hom).sheaf d P.sheaf)
    {n : ℕ} (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left ⟶ P.sheaf))
    (hs : ∀ x : A.abelian.scheme.left, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (he : IsClosedImmersion (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom s hs).left)
    (hPresentations : Hilbert.EndomorphismEquationsInput.{0})
    (hc : ∀ x : S, IsUnit (D.conductor : S.presheaf.stalk x)) (Q : Polynomial ℚ) :
    ∃ Z : Over S, IsReduced Z.left ∧ LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsSeparated Z.hom ∧
      (∀ z : Z.left, Z.hom z ∈ Relative.CMGraphSourcePolynomial.relativeCMPolynomialOpen D
        (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he) Q) ∧
      ∃ ρZ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback Z.hom),
        ∀ (T : Over S) [IsReduced T.left]
          (_hT : ∀ t : T.left, T.hom t ∈ Relative.CMGraphSourcePolynomial.relativeCMPolynomialOpen D
            (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he) Q)
          (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback T.hom)),
          AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback T.hom) ρ →
            ∃! f : T ⟶ Z, Integral.ActionScheme.restrictIntegralAction A.abelian ρZ f = ρ := by
  let BA := SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he
  let U := Relative.CMGraphSourcePolynomial.relativeCMPolynomialOpen D BA Q
  obtain ⟨B, L, M, hB, hft, hqc, hsep, ρM, _, hclass⟩ :=
    ActionScheme.exists_e34_bounded_integral_action_scheme A.abelian D hPresentations BA hc (fun _ => Q)
  let Z := M.solutionScheme
  let := hft
  let := hqc
  let := hsep
  let : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  let : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  let : IsNoetherian Z.left := ⟨⟩
  let V := Z.hom ⁻¹ᵁ U
  let W := AbelianModuli.HilbertConstruction.Open.ParameterPoints.openParameterScheme Z V
  let j := AbelianModuli.HilbertConstruction.Open.ParameterPoints.openParameterInclusion Z V
  have : LocallyOfFiniteType W.hom := inferInstanceAs (LocallyOfFiniteType (V.ι ≫ Z.hom))
  have : QuasiCompact W.hom := inferInstanceAs (QuasiCompact (V.ι ≫ Z.hom))
  have : IsSeparated W.hom := inferInstanceAs (IsSeparated (V.ι ≫ Z.hom))
  let q : Reduction.reduction W ⟶ Z := Reduction.reductionι W ≫ j
  let ρR := Integral.ActionScheme.restrictIntegralAction A.abelian ρM q
  have : Mono j := Over.mono_of_mono_left j
  have : Mono q := inferInstanceAs (Mono (Reduction.reductionι W ≫ j))
  refine ⟨Reduction.reduction W, inferInstance, inferInstance, inferInstance, inferInstance,
    fun z => ((Reduction.reductionι W).left z).property, ρR, ?_⟩
  intro T hred hT ρ hρ
  obtain ⟨f, hf, huniq⟩ := (hclass T ρ).mp
    (D.relative_e34_integral_generator_on_stratum A P d hP s hs he B hB Q T hT ρ hρ)
  have hrange : Set.range f.left ⊆ (V : Set Z.left) := by
    rintro _ ⟨t, rfl⟩
    change Z.hom (f.left t) ∈ U
    have hw := congrArg (fun h : T.left ⟶ S => h t) f.w
    exact hw.symm ▸ hT t
  let l : T ⟶ W := (AbelianModuli.HilbertConstruction.Open.ParameterPoints.openParameterPointEquiv Z V T).symm ⟨f, hrange⟩
  have hl : l ≫ j = f := congrArg Subtype.val
    ((AbelianModuli.HilbertConstruction.Open.ParameterPoints.openParameterPointEquiv Z V T).apply_symm_apply ⟨f, hrange⟩)
  let c := Reduction.factorToReduction l
  have hcf : c ≫ q = f := by
    change Reduction.factorToReduction l ≫ (Reduction.reductionι W ≫ j) = f
    rw [← Category.assoc, Reduction.factorToReduction_ι, hl]
  refine ⟨c, ?_, ?_⟩
  · change Integral.ActionScheme.restrictIntegralAction A.abelian (Integral.ActionScheme.restrictIntegralAction A.abelian ρM q) c = ρ
    rw [← Integral.ActionScheme.restrictIntegralAction_comp, hcf]
    exact hf
  · intro e heq
    apply (cancel_mono q).mp
    rw [hcf]
    apply huniq
    rw [Integral.ActionScheme.restrictIntegralAction_comp]
    exact heq

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.RelativeStratumActionAmbient
