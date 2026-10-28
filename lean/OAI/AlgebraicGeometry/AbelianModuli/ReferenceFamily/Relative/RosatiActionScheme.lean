import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.IntegralActionAmbient
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.RosatiActionCutdown

/-! # Rosati Action Scheme -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.RosatiActionScheme

noncomputable section

/-! Construct the bounded relative Rosati-action scheme of a varying
polarized family with a canonical section embedding. All polynomial
strata are assembled, and every test is classified exactly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_relative_rosati_action_scheme
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
    (hc : ∀ x : S, IsUnit (D.conductor : S.presheaf.stalk x)) :
    ∃ Z : Over S, LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsSeparated Z.hom ∧
      ∃ ρZ : ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback Z.hom),
        ActionData.RosatiConjugation (A.pullback Z.hom) ρZ ∧
        ∀ (T : Over S)
          (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback T.hom)),
          ActionData.RosatiConjugation (A.pullback T.hom) ρ ↔
            ∃! f : T ⟶ Z, PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian ρZ f = ρ := by
  obtain ⟨Z, hft, hqc, hsep, ρZ, hZ⟩ :=
    IntegralActionAmbient.exists_relative_integral_action_ambient D A P d hP s hs he hc
  let := hft
  let := hqc
  let := hsep
  let : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  let : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  let : IsNoetherian Z.left := ⟨⟩
  let BA := PELModuli.IntegralModel.SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he
  obtain ⟨W, j, hj, hρW, hclass⟩ := RosatiActionCutdown.exists_projective_relative_rosati_action_cutdown A Z
    (PELModuli.IntegralModel.Presentations.EquationBaseChange.e34ProjectivePresentationBaseChange BA Z.hom) ρZ
  let := hj
  have : Mono j := Over.mono_of_mono_left j
  have hWft : LocallyOfFiniteType W.hom := by
    rw [← j.w]
    infer_instance
  have hWqc : QuasiCompact W.hom := by
    rw [← j.w]
    infer_instance
  have hWsep : IsSeparated W.hom := by
    rw [← j.w]
    infer_instance
  let ρW := PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian ρZ j
  refine ⟨W, hWft, hWqc, hWsep, ρW, hρW, ?_⟩
  intro T ρ
  constructor
  · intro hρ
    obtain ⟨f, hf, huniq⟩ := hZ T ρ hρ
    have hρf : ActionData.RosatiConjugation (A.pullback T.hom) (PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian ρZ f) :=
      hf.symm ▸ hρ
    obtain ⟨c, hc, _⟩ := (hclass T f).mp hρf
    refine ⟨c, ?_, ?_⟩
    · change PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian (PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian ρZ j) c = ρ
      rw [← PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction_comp, hc]
      exact hf
    · intro e heq
      apply (cancel_mono j).mp
      rw [hc]
      apply huniq
      rw [PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction_comp]
      exact heq
  · rintro ⟨f, hf, _⟩
    exact hf ▸ PELModuli.IntegralModel.RosatiRestriction.rosati_restrictIntegralAction (T := T) (U := W) A ρW hρW f

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.RosatiActionScheme
