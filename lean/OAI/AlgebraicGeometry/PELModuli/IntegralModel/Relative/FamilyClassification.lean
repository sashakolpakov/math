import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GlobalRelativeAction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.Transport

/-! # Family Classification -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FamilyClassification

noncomputable section

section

/-! The represented action is an actual universal integral PEL family.
Its functor restriction agrees with geometric pullback through the canonical
polarization-, level-, Poincare-, and action-preserving isomorphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s N : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N M.left)

def relativePELUniversal (Z : Over M.left)
    (u : (ActionFunctor.relativePELActionFunctor P iotaO M A).obj (op Z)) :
    PEL.Has.IntegralPELObject P R iotaO N ((Over.map M.hom).obj Z) where
  data := { polarized := A.pullback Z.hom, action := u.val }
  rosati := u.property.1
  lieRanks := u.property.2

def relativePELUniversal_restrictionIso {T Z : Over M.left}
    (u : (ActionFunctor.relativePELActionFunctor P iotaO M A).obj (op Z)) (f : T ⟶ Z) :
    PEL.Iso.PolarizedActionIso ((relativePELUniversal P iotaO M A Z u).data.pullback f.left)
      (relativePELUniversal P iotaO M A T ((ActionFunctor.relativePELActionFunctor P iotaO M A).map f.op u)).data where
  polarized := RosatiRestriction.polarizedRestrictionIso A f
  action a := by
    change (Over.pullback f.left).map (u.val.map a) ≫ (RosatiRestriction.polarizedRestrictionIso A f).abelian.hom =
      (RosatiRestriction.polarizedRestrictionIso A f).abelian.hom ≫ (Integral.ActionScheme.restrictIntegralAction A.abelian u.val f).map a
    rw [RosatiRestriction.polarizedRestrictionIso_abelian]
    exact (Iso.hom_inv_id_assoc _ _).symm

end

/-! Bounded relative action representability supplies a geometric
classifier for every integral PEL family with a chosen polarized comparison
to the fixed family. No action or classifier is assumed to exist. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s N : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N M.left)

theorem exists_bounded_relative_pel_universal_family [IsNoetherian M.left]
    (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E) (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (hc : ∀ x : M.left, IsUnit (D.conductor : M.left.presheaf.stalk x)) :
    ∃ Z : Over M.left, IsReduced Z.left ∧ IsNoetherian Z.left ∧
      LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsSeparated Z.hom ∧
      ∃ U : PEL.Has.IntegralPELObject P R iotaO N ((Over.map M.hom).obj Z),
        U.data.polarized = A.pullback Z.hom ∧
        ∀ (T : Over M.left) [IsReduced T.left]
          (B : PEL.Has.IntegralPELObject P R iotaO N ((Over.map M.hom).obj T)),
          Nonempty (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) B.data.polarized) →
          ∃ f : T ⟶ Z, Nonempty (PEL.Iso.PolarizedActionIso (U.data.pullback f.left) B.data) := by
  obtain ⟨Z, hr, hn, hft, hqc, hs, u, hclass⟩ :=
    GlobalRelativeAction.exists_global_relative_pel_action_representation P iotaO M A D hPresentations hc
  refine ⟨Z, hr, hn, hft, hqc, hs, relativePELUniversal P iotaO M A Z u, rfl, ?_⟩
  rintro T _ B ⟨e⟩
  let B' := B.transport e.symm
  let v : (ActionFunctor.relativePELActionFunctor P iotaO M A).obj (op T) :=
    ⟨B'.data.action, B'.rosati, B'.lieRanks⟩
  obtain ⟨f, hf⟩ := (hclass T).surjective v
  change (ActionFunctor.relativePELActionFunctor P iotaO M A).map f.op u = v at hf
  have ei : PEL.Iso.PolarizedActionIso
      (relativePELUniversal P iotaO M A T ((ActionFunctor.relativePELActionFunctor P iotaO M A).map f.op u)).data
      B'.data := by
    rw [hf]
    exact PEL.Iso.PolarizedActionIso.refl B'.data
  exact ⟨f, ⟨(relativePELUniversal_restrictionIso P iotaO M A u f).trans
    (ei.trans (B.transportIso e.symm).symm)⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FamilyClassification
