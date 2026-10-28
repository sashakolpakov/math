import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.RelativeRosatiScheme
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.LieActionCutdown

/-! # Relative Action Scheme -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.RelativeActionScheme

noncomputable section

/-! The full corrected Presentations input, computed CM bounds, and actual Lie
rank loci construct the integral PEL-action scheme over a varying
polarized family with a canonical section embedding. Its universal
action satisfies both literal PEL conditions on all reduced tests. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_e34_reduced_relative_pel_action_scheme
    {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    {s N : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    [IsAffine M.left] [IsLocallyNoetherian M.left]
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N M.left)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.abelian.scheme.left) (d : ℕ)
    (hL : AbelianModuli.HilbertConstruction.Tensor.Powers.IsTensorPower (Relative.PoincareSimilitude.RelativePoincareClasses.polarizationLine A.dual
      A.polarization.isogeny.hom).sheaf d L.sheaf)
    {n : ℕ} (q : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left ⟶ L.sheaf))
    (hq : ∀ x : A.abelian.scheme.left, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (q i))
    (he : IsClosedImmersion (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom q hq).left)
    (hPresentations : Hilbert.EndomorphismEquationsInput.{0})
    (hc : ∀ x : M.left, IsUnit (D.conductor : M.left.presheaf.stalk x)) :
    ∃ Z : Over M.left, IsReduced Z.left ∧ LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsSeparated Z.hom ∧
      ∃ ρZ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback Z.hom),
        AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback Z.hom) ρZ ∧
        PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map M.hom).obj Z) (A.abelian.pullback Z.hom) ρZ ∧
        ∀ (T : Over M.left) [IsReduced T.left]
          (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback T.hom)),
          (AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback T.hom) ρ ∧
            PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map M.hom).obj T) (A.abelian.pullback T.hom) ρ) ↔
            ∃! f : T ⟶ Z, Integral.ActionScheme.restrictIntegralAction A.abelian ρZ f = ρ := by
  obtain ⟨Z, hr, hft, hqc, hsep, ρZ, hρZ, hZ⟩ :=
    RelativeRosatiScheme.exists_e34_reduced_relative_rosati_action_scheme D A L d hL q hq he hPresentations hc
  let := hr
  let := hft
  let := hqc
  let := hsep
  let : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  let : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  let : IsNoetherian Z.left := ⟨⟩
  obtain ⟨W, j, hW, hj, hjqc, hLieW, hclass⟩ :=
    Relative.LieActionCutdown.exists_reduced_relative_lie_action_cutdown P iotaO M A.abelian Z ρZ
  let := hj
  let := hjqc
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
  have hρW := RosatiRestriction.rosati_restrictIntegralAction (T := W) (U := Z) A ρZ hρZ j
  refine ⟨W, hW, hWft, hWqc, hWsep, ρW, hρW, hLieW, ?_⟩
  intro T hT ρ
  constructor
  · rintro ⟨hρ, hLie⟩
    obtain ⟨f, hf, huniq⟩ := (hZ T ρ).mp hρ
    have hLief : PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map M.hom).obj T) (A.abelian.pullback T.hom)
        (Integral.ActionScheme.restrictIntegralAction A.abelian ρZ f) := hf.symm ▸ hLie
    obtain ⟨c, hc, _⟩ := (hclass T f).mp hLief
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
    refine ⟨hf ▸ RosatiRestriction.rosati_restrictIntegralAction (T := T) (U := W) A ρW hρW f, ?_⟩
    have hLf := (hclass T (f ≫ j)).mpr
      ⟨f, rfl, fun a ha => (cancel_mono j).mp ha⟩
    rw [Integral.ActionScheme.restrictIntegralAction_comp] at hLf
    exact hf ▸ hLf

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.RelativeActionScheme
