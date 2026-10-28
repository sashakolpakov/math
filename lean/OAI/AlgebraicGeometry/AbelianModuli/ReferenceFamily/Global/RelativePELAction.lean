import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PELActionAtlas
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.AtlasUniversalValue
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AtlasGlobalClassification
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.TestBaseCover
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ActionSeparation

/-! # Relative PEL Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.RelativePELAction

noncomputable section

/-! Global bounded representability of integral PEL actions on an actual
varying polarized family over a noetherian base. The parameter scheme,
universal action, and all-test classifiers are constructed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [Algebra ℚ R] {s N : ℕ} (P : Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N M.left)

theorem exists_global_relative_pel_action_representation [IsNoetherian M.left]
    (D : PELModuli.IntegralModel.CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    (hc : ∀ x : M.left, IsUnit (D.conductor : M.left.presheaf.stalk x)) :
    ∃ Z : Over M.left, IsNoetherian Z.left ∧
      LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsSeparated Z.hom ∧
      ∃ u : (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).obj (op Z),
        ∀ (T : Over M.left), Function.Bijective
          (fun f : T ⟶ Z => (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).map f.op u) := by
  let L := Relative.PELActionAtlas.RelativePELActionAtlas.localRepresentation P iotaO M A D hc
  let Z := Relative.PELActionAtlas.RelativePELActionAtlas.parameter P iotaO M A D hc
  have : IsNoetherian (RepresentationAtlasIs.RepresentationAtlas.scheme L) :=
    inferInstanceAs (IsNoetherian Z.left)
  obtain ⟨u, hu⟩ := PEL.AtlasUniversalValue.exists_pel_atlas_universal_value P iotaO M A L
  refine ⟨Z, inferInstance, inferInstance, inferInstance, inferInstance, u,
    fun T => ?_⟩
  let U := fun V : M.left.affineOpens => V.val
  have hU : iSup U = ⊤ := iSup_affineOpens_eq_top M.left
  exact AtlasGlobalClassification.RepresentationAtlas.classifies_of_source_cover L u hu T
    (PELModuli.IntegralModel.Reduced.TestBaseCover.testBaseOpenCover U hU T) (fun i => i)
    (PELModuli.IntegralModel.Reduced.TestBaseCover.testBaseOpenCover_mapsTo U hU T)
    (PELModuli.IntegralModel.Relative.ActionSeparation.relativePELAction_cover_separated P iotaO M A T (PELModuli.IntegralModel.Reduced.TestBaseCover.testBaseOpenCover U hU T))

theorem exists_global_bounded_relative_pel_action_scheme [IsNoetherian M.left]
    (D : PELModuli.IntegralModel.CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    (hc : ∀ x : M.left, IsUnit (D.conductor : M.left.presheaf.stalk x)) :
    ∃ Z : Over M.left, IsNoetherian Z.left ∧
      LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsSeparated Z.hom ∧
      ∃ ρZ : ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback Z.hom),
        ActionData.RosatiConjugation (A.pullback Z.hom) ρZ ∧
        PELModuli.IntegralModel.PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map M.hom).obj Z) (A.abelian.pullback Z.hom) ρZ ∧
        ∀ (T : Over M.left)
          (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback T.hom)),
          (ActionData.RosatiConjugation (A.pullback T.hom) ρ ∧
            PELModuli.IntegralModel.PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map M.hom).obj T) (A.abelian.pullback T.hom) ρ) ↔
          ∃! f : T ⟶ Z, PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian ρZ f = ρ := by
  obtain ⟨Z, hn, hft, hqc, hs, u, hclass⟩ :=
    exists_global_relative_pel_action_representation P iotaO M A D hc
  refine ⟨Z, hn, hft, hqc, hs, u.val, u.property.1, u.property.2, fun T ρ => ?_⟩
  constructor
  · intro hρ
    let v : (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).obj (op T) := ⟨ρ, hρ⟩
    obtain ⟨f, hf⟩ := (hclass T).surjective v
    refine ⟨f, congrArg Subtype.val hf, fun g hg => ?_⟩
    apply (hclass T).injective
    exact (Subtype.ext hg).trans hf.symm
  · rintro ⟨f, hf, _⟩
    have h := ((PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).map f.op u).property
    exact hf ▸ h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.RelativePELAction
