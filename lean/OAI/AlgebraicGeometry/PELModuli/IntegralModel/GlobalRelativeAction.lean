import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ActionAtlas
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.AtlasUniversalValue
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.AtlasGlobalClassification
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.TestBaseCover
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ActionSeparation

/-! # Global Relative Action -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.GlobalRelativeAction

noncomputable section

/-! Global bounded representability of integral PEL actions on an actual
varying polarized family over a noetherian base. The parameter scheme,
universal action, and all reduced-test classifiers are constructed. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s N : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N M.left)

theorem exists_global_relative_pel_action_representation [IsNoetherian M.left]
    (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E) (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (hc : ∀ x : M.left, IsUnit (D.conductor : M.left.presheaf.stalk x)) :
    ∃ Z : Over M.left, IsReduced Z.left ∧ IsNoetherian Z.left ∧
      LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsSeparated Z.hom ∧
      ∃ u : (Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).obj (op Z),
        ∀ (T : Over M.left) [IsReduced T.left], Function.Bijective
          (fun f : T ⟶ Z => (Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).map f.op u) := by
  let L := Relative.ActionAtlas.RelativePELActionAtlas.localRepresentation P iotaO M A D hPresentations hc
  let Z := Relative.ActionAtlas.RelativePELActionAtlas.parameter P iotaO M A D hPresentations hc
  have : IsNoetherian (Reduced.RepresentationAtlas.ReducedRepresentationAtlas.scheme L) :=
    inferInstanceAs (IsNoetherian Z.left)
  obtain ⟨u, hu⟩ := PEL.AtlasUniversalValue.exists_pel_atlas_universal_value P iotaO M A L
  refine ⟨Z, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, u,
    fun T _ => ?_⟩
  let U := fun V : M.left.affineOpens => V.val
  have hU : iSup U = ⊤ := iSup_affineOpens_eq_top M.left
  exact Reduced.AtlasGlobalClassification.ReducedRepresentationAtlas.classifies_of_source_cover L u hu T
    (Reduced.TestBaseCover.testBaseOpenCover U hU T) (fun i => i)
    (Reduced.TestBaseCover.testBaseOpenCover_mapsTo U hU T)
    (Relative.ActionSeparation.relativePELAction_cover_separated P iotaO M A T (Reduced.TestBaseCover.testBaseOpenCover U hU T))

theorem exists_global_bounded_relative_pel_action_scheme [IsNoetherian M.left]
    (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E) (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (hc : ∀ x : M.left, IsUnit (D.conductor : M.left.presheaf.stalk x)) :
    ∃ Z : Over M.left, IsReduced Z.left ∧ IsNoetherian Z.left ∧
      LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsSeparated Z.hom ∧
      ∃ ρZ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback Z.hom),
        AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback Z.hom) ρZ ∧
        PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map M.hom).obj Z) (A.abelian.pullback Z.hom) ρZ ∧
        ∀ (T : Over M.left) [IsReduced T.left]
          (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback T.hom)),
          (AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback T.hom) ρ ∧
            PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map M.hom).obj T) (A.abelian.pullback T.hom) ρ) ↔
          ∃! f : T ⟶ Z, Integral.ActionScheme.restrictIntegralAction A.abelian ρZ f = ρ := by
  obtain ⟨Z, hr, hn, hft, hqc, hs, u, hclass⟩ :=
    exists_global_relative_pel_action_representation P iotaO M A D hPresentations hc
  refine ⟨Z, hr, hn, hft, hqc, hs, u.val, u.property.1, u.property.2, fun T _ ρ => ?_⟩
  constructor
  · intro hρ
    let v : (Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).obj (op T) := ⟨ρ, hρ⟩
    obtain ⟨f, hf⟩ := (hclass T).surjective v
    refine ⟨f, congrArg Subtype.val hf, fun g hg => ?_⟩
    apply (hclass T).injective
    exact (Subtype.ext hg).trans hf.symm
  · rintro ⟨f, hf, _⟩
    have h := ((Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).map f.op u).property
    exact hf ▸ h

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.GlobalRelativeAction
