import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.PELId
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FixedComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AddedLevelRestriction

/-! # Added Family -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.AddedFamily

noncomputable section

/-! The represented relative action is an actual two-level integral PEL
family. Its geometric classifier preserves both chosen markings through
the prescribed comparison, on all reduced test schemes. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    (A : AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel (3 * s) P.polarizationType L N M.left)

def relativeAddedPELUniversal (Z : Over M.left)
    (u : (ActionFunctor.relativePELActionFunctor P iotaO M A.auxiliary).obj (op Z)) :
    IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N ((Over.map M.hom).obj Z) where
  auxiliary := FamilyClassification.relativePELUniversal P iotaO M A.auxiliary Z u
  prescribed := A.prescribed.pullback Z.hom

theorem relativeAddedPELUniversal_classifying
    {T Z : Over M.left} (u : (ActionFunctor.relativePELActionFunctor P iotaO M A.auxiliary).obj (op Z))
    (hclass : Function.Surjective (fun f : T ⟶ Z =>
      (ActionFunctor.relativePELActionFunctor P iotaO M A.auxiliary).map f.op u))
    (B : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N ((Over.map M.hom).obj T))
    (e : AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel.Iso (A.pullback T.hom) B.pure) :
    ∃ f : T ⟶ Z, Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso
      ((relativeAddedPELUniversal P iotaO M A Z u).pullback ((Over.map M.hom).map f)) B) := by
  obtain ⟨f, a, ha⟩ := FixedComparison.relativePELUniversal_classifying_with_comparison P iotaO M A.auxiliary
    u hclass B.auxiliary e.auxiliary
  refine ⟨f, ⟨{ auxiliary := a, prescribed := ?_ }⟩⟩
  let b := (AddedLevelRestriction.addedLevelRestrictionIso A f).trans e
  apply AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  intro V c
  let β := (A.prescribed.pullback Z.hom).pullback f.left
  change (β.hom.app (op V) c).val ≫ a.polarized.abelian.hom = _
  exact (congrArg ((β.hom.app (op V) c).val ≫ ·) ha).trans (b.prescribed_basis V c)

theorem exists_bounded_relative_added_pel_universal_family [IsNoetherian M.left]
    (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E) (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (hc : ∀ x : M.left, IsUnit (D.conductor : M.left.presheaf.stalk x)) :
    ∃ Z : Over M.left, IsReduced Z.left ∧ IsNoetherian Z.left ∧
      LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsSeparated Z.hom ∧
      ∃ U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N ((Over.map M.hom).obj Z),
        U.pure = A.pullback Z.hom ∧
        ∀ (T : Over M.left) [IsReduced T.left]
          (B : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N ((Over.map M.hom).obj T)),
          Nonempty (AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel.Iso (A.pullback T.hom) B.pure) →
          ∃ f : T ⟶ Z, Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso
            (U.pullback ((Over.map M.hom).map f)) B) := by
  obtain ⟨Z, hr, hn, hft, hqc, hs, u, hclass⟩ :=
    GlobalRelativeAction.exists_global_relative_pel_action_representation P iotaO M A.auxiliary D hPresentations hc
  refine ⟨Z, hr, hn, hft, hqc, hs, relativeAddedPELUniversal P iotaO M A Z u, rfl, ?_⟩
  rintro T _ B ⟨e⟩
  exact relativeAddedPELUniversal_classifying P iotaO M A u (hclass T).surjective B e

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.AddedFamily
