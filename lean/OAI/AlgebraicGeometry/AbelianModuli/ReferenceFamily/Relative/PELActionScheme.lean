import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.RosatiActionScheme
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.LieActionCutdown

/-! # PEL Action Scheme -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PELActionScheme

noncomputable section

/-! Proved projective Hom and equation loci, computed CM graph bounds,
and the clopen Lie locus construct the integral PEL-action scheme.
Its universal action and classification use the original conditions
on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_embedded_relative_pel_action_scheme
    {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [Algebra ℚ R] (D : PELModuli.IntegralModel.CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    {s N : ℕ} (P : Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    [IsAffine M.left] [IsLocallyNoetherian M.left]
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N M.left)
    (L : HilbertConstruction.Line.Bundles.LineBundle A.abelian.scheme.left) (d : ℕ)
    (hL : HilbertConstruction.Tensor.Powers.IsTensorPower (PELModuli.IntegralModel.Relative.PoincareSimilitude.RelativePoincareClasses.polarizationLine A.dual
      A.polarization.isogeny.hom).sheaf d L.sheaf)
    {n : ℕ} (q : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left ⟶ L.sheaf))
    (hq : ∀ x : A.abelian.scheme.left, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (q i))
    (he : IsClosedImmersion (HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom q hq).left)
    (hc : ∀ x : M.left, IsUnit (D.conductor : M.left.presheaf.stalk x)) :
    ∃ Z : Over M.left, LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsSeparated Z.hom ∧
      ∃ ρZ : ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback Z.hom),
        ActionData.RosatiConjugation (A.pullback Z.hom) ρZ ∧
        PELModuli.IntegralModel.PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map M.hom).obj Z) (A.abelian.pullback Z.hom) ρZ ∧
        ∀ (T : Over M.left)
          (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback T.hom)),
          (ActionData.RosatiConjugation (A.pullback T.hom) ρ ∧
            PELModuli.IntegralModel.PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map M.hom).obj T) (A.abelian.pullback T.hom) ρ) ↔
            ∃! f : T ⟶ Z, PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian ρZ f = ρ := by
  obtain ⟨Z, hft, hqc, hsep, ρZ, hρZ, hZ⟩ :=
    RosatiActionScheme.exists_relative_rosati_action_scheme D A L d hL q hq he hc
  let := hft
  let := hqc
  let := hsep
  let : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  let : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  let : IsNoetherian Z.left := ⟨⟩
  obtain ⟨W, j, hj, hjclosed, hLieW, hclass⟩ :=
    LieActionCutdown.exists_relative_lie_action_cutdown P iotaO M A.abelian Z ρZ
  let := hj
  let := hjclosed
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
  have hρW := PELModuli.IntegralModel.RosatiRestriction.rosati_restrictIntegralAction (T := W) (U := Z) A ρZ hρZ j
  refine ⟨W, hWft, hWqc, hWsep, ρW, hρW, hLieW, ?_⟩
  intro T ρ
  constructor
  · rintro ⟨hρ, hLie⟩
    obtain ⟨f, hf, huniq⟩ := (hZ T ρ).mp hρ
    have hLief : PELModuli.IntegralModel.PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map M.hom).obj T) (A.abelian.pullback T.hom)
        (PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian ρZ f) := hf.symm ▸ hLie
    obtain ⟨c, hc, _⟩ := (hclass T f).mp hLief
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
    refine ⟨hf ▸ PELModuli.IntegralModel.RosatiRestriction.rosati_restrictIntegralAction (T := T) (U := W) A ρW hρW f, ?_⟩
    have hLf := (hclass T (f ≫ j)).mpr
      ⟨f, rfl, fun a ha => (cancel_mono j).mp ha⟩
    rw [PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction_comp] at hLf
    exact hf ▸ hLf

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PELActionScheme
