import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BoundedIntegralActionScheme
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.CMStratumGraphBound
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.ParameterPoints

/-! # Stratum Integral Action Ambient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StratumIntegralActionAmbient

noncomputable section

/-! On each computed CM polynomial stratum, retain the original scheme
of integral actions and its universal action. Every Rosati action over
an arbitrary test scheme has a unique classifying morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.ParameterPoints

theorem exists_stratum_integral_action_ambient
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    (D : PELModuli.IntegralModel.CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    {S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
    {g N : ℕ} {δ : Fin g → ℕ} (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (P : HilbertConstruction.Line.Bundles.LineBundle A.abelian.scheme.left) (d : ℕ)
    (hP : HilbertConstruction.Tensor.Powers.IsTensorPower (PELModuli.IntegralModel.Relative.PoincareSimilitude.RelativePoincareClasses.polarizationLine A.dual
      A.polarization.isogeny.hom).sheaf d P.sheaf)
    {n : ℕ} (s : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left ⟶ P.sheaf))
    (hs : ∀ x : A.abelian.scheme.left, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (he : IsClosedImmersion (HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom s hs).left)
    (hc : ∀ x : S, IsUnit (D.conductor : S.presheaf.stalk x)) (Q : Polynomial ℚ) :
    ∃ Z : Over S, LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsSeparated Z.hom ∧
      (∀ z : Z.left, Z.hom z ∈ PELModuli.IntegralModel.Relative.CMGraphSourcePolynomial.relativeCMPolynomialOpen D
        (PELModuli.IntegralModel.SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he) Q) ∧
      ∃ ρZ : ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback Z.hom),
        ∀ (T : Over S)
          (_hT : ∀ t : T.left, T.hom t ∈ PELModuli.IntegralModel.Relative.CMGraphSourcePolynomial.relativeCMPolynomialOpen D
            (PELModuli.IntegralModel.SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he) Q)
          (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback T.hom)),
          ActionData.RosatiConjugation (A.pullback T.hom) ρ →
            ∃! f : T ⟶ Z, PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian ρZ f = ρ := by
  let BA := PELModuli.IntegralModel.SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he
  let U := PELModuli.IntegralModel.Relative.CMGraphSourcePolynomial.relativeCMPolynomialOpen D BA Q
  obtain ⟨B, L, M, hB, hft, hqc, hsep, ρM, _, hclass⟩ :=
    BoundedIntegralActionScheme.exists_bounded_integral_action_scheme A.abelian D BA hc (fun _ => Q)
  let Z := M.solutionScheme
  let := hft
  let := hqc
  let := hsep
  let : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  let : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  let : IsNoetherian Z.left := ⟨⟩
  let V := Z.hom ⁻¹ᵁ U
  let W := HilbertConstruction.Open.ParameterPoints.openParameterScheme Z V
  let j := HilbertConstruction.Open.ParameterPoints.openParameterInclusion Z V
  have hWft : LocallyOfFiniteType W.hom :=
    inferInstanceAs (LocallyOfFiniteType (V.ι ≫ Z.hom))
  have hWqc : QuasiCompact W.hom := inferInstanceAs (QuasiCompact (V.ι ≫ Z.hom))
  have hWsep : IsSeparated W.hom := inferInstanceAs (IsSeparated (V.ι ≫ Z.hom))
  let ρW := PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian ρM j
  have : Mono j := Over.mono_of_mono_left j
  refine ⟨W, hWft, hWqc, hWsep, fun z => z.property, ρW, ?_⟩
  intro T hT ρ hρ
  obtain ⟨f, hf, huniq⟩ := (hclass T ρ).mp
    (D.relative_e34_integral_generator_on_stratum A P d hP s hs he B hB Q T hT ρ hρ)
  have hrange : Set.range f.left ⊆ (V : Set Z.left) := by
    rintro _ ⟨t, rfl⟩
    change Z.hom (f.left t) ∈ U
    have hw := congrArg (fun h : T.left ⟶ S => h t) f.w
    exact hw.symm ▸ hT t
  let l : T ⟶ W := (HilbertConstruction.Open.ParameterPoints.openParameterPointEquiv Z V T).symm ⟨f, hrange⟩
  have hl : l ≫ j = f := congrArg Subtype.val
    ((HilbertConstruction.Open.ParameterPoints.openParameterPointEquiv Z V T).apply_symm_apply ⟨f, hrange⟩)
  refine ⟨l, ?_, ?_⟩
  · change PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian (PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian ρM j) l = ρ
    rw [← PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction_comp, hl]
    exact hf
  · intro e heq
    apply (cancel_mono j).mp
    rw [hl]
    apply huniq
    rw [PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction_comp]
    exact heq

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StratumIntegralActionAmbient
