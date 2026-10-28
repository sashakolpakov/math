import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.RelativeActionAmbient
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.RosatiActionCutdown

/-! # Relative Rosati Scheme -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.RelativeRosatiScheme

noncomputable section

/-! Construct the bounded relative Rosati-action scheme of a varying
polarized family with a canonical section embedding. All polynomial
strata are assembled, and every reduced test is classified exactly. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_e34_reduced_relative_rosati_action_scheme
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
    (hc : ∀ x : S, IsUnit (D.conductor : S.presheaf.stalk x)) :
    ∃ Z : Over S, IsReduced Z.left ∧ LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsSeparated Z.hom ∧
      ∃ ρZ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback Z.hom),
        AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback Z.hom) ρZ ∧
        ∀ (T : Over S) [IsReduced T.left]
          (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback T.hom)),
          AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback T.hom) ρ ↔
            ∃! f : T ⟶ Z, Integral.ActionScheme.restrictIntegralAction A.abelian ρZ f = ρ := by
  obtain ⟨Z, hr, hft, hqc, hsep, ρZ, hZ⟩ :=
    RelativeActionAmbient.exists_e34_reduced_relative_action_ambient D A P d hP s hs he hPresentations hc
  let := hr
  let := hft
  let := hqc
  let := hsep
  let : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  let : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  let : IsNoetherian Z.left := ⟨⟩
  obtain ⟨W, j, hW, hj, hρW, hclass⟩ := Relative.RosatiActionCutdown.exists_reduced_relative_rosati_action_cutdown A Z ρZ
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
  let ρW := Integral.ActionScheme.restrictIntegralAction A.abelian ρZ j
  refine ⟨W, hW, hWft, hWqc, hWsep, ρW, hρW, ?_⟩
  intro T hT ρ
  constructor
  · intro hρ
    obtain ⟨f, hf, huniq⟩ := hZ T ρ hρ
    have hρf : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback T.hom) (Integral.ActionScheme.restrictIntegralAction A.abelian ρZ f) :=
      hf.symm ▸ hρ
    obtain ⟨c, hc, _⟩ := (hclass T f).mp hρf
    refine ⟨c, ?_, ?_⟩
    · change Integral.ActionScheme.restrictIntegralAction A.abelian (Integral.ActionScheme.restrictIntegralAction A.abelian ρZ j) c = ρ
      rw [← Integral.ActionScheme.restrictIntegralAction_comp, hc]
      exact hf
    · intro e heq
      apply (cancel_mono j).mp
      rw [hc]
      apply huniq
      rw [Integral.ActionScheme.restrictIntegralAction_comp]
      exact heq
  · rintro ⟨f, hf, _⟩
    exact hf ▸ RosatiRestriction.rosati_restrictIntegralAction (T := T) (U := W) A ρW hρW f

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.RelativeRosatiScheme
