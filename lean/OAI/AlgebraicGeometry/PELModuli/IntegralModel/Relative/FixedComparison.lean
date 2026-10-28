import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FamilyClassification

/-! # Fixed Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FixedComparison

noncomputable section

/-! The relative PEL classifier retains a prescribed polarized comparison.
Thus additional full levels can be transported through the actual universal
family isomorphism, without assuming its existence or forgetting the marking. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s N : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N M.left)

theorem relativePELUniversal_classifying_with_comparison
    {T Z : Over M.left} (u : (ActionFunctor.relativePELActionFunctor P iotaO M A).obj (op Z))
    (hclass : Function.Surjective (fun f : T ⟶ Z => (ActionFunctor.relativePELActionFunctor P iotaO M A).map f.op u))
    (B : PEL.Has.IntegralPELObject P R iotaO N ((Over.map M.hom).obj T))
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) B.data.polarized) :
    ∃ (f : T ⟶ Z) (a : PEL.Iso.PolarizedActionIso
      ((FamilyClassification.relativePELUniversal P iotaO M A Z u).data.pullback f.left) B.data),
      a.polarized.abelian.hom = (RosatiRestriction.polarizedRestrictionIso A f).abelian.hom ≫ e.abelian.hom := by
  let B' := B.transport e.symm
  let v : (ActionFunctor.relativePELActionFunctor P iotaO M A).obj (op T) :=
    ⟨B'.data.action, B'.rosati, B'.lieRanks⟩
  obtain ⟨f, hf⟩ := hclass v
  let a : PEL.Iso.PolarizedActionIso
      (FamilyClassification.relativePELUniversal P iotaO M A T ((ActionFunctor.relativePELActionFunctor P iotaO M A).map f.op u)).data
      B'.data := {
    polarized := AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.refl (A.pullback T.hom)
    action x := by
      have hx := congrArg (fun w : (ActionFunctor.relativePELActionFunctor P iotaO M A).obj (op T) => w.val.map x) hf
      change ((ActionFunctor.relativePELActionFunctor P iotaO M A).map f.op u).val.map x ≫ 𝟙 _ =
        𝟙 _ ≫ B'.data.action.map x
      exact (Category.comp_id _).trans (hx.trans (Category.id_comp _).symm) }
  let j := (FamilyClassification.relativePELUniversal_restrictionIso P iotaO M A u f).trans
    (a.trans (B.transportIso e.symm).symm)
  refine ⟨f, j, ?_⟩
  change (RosatiRestriction.polarizedRestrictionIso A f).abelian.hom ≫
    (𝟙 (A.abelian.pullback T.hom).scheme ≫ e.abelian.hom) =
      (RosatiRestriction.polarizedRestrictionIso A f).abelian.hom ≫ e.abelian.hom
  exact congrArg ((RosatiRestriction.polarizedRestrictionIso A f).abelian.hom ≫ ·) (Category.id_comp e.abelian.hom)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FixedComparison
