import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FamilyClassification

/-! # Family Uniqueness -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FamilyUniqueness

noncomputable section

/-! The constructed relative action parameter has unique geometric
classifiers when automorphisms of the fixed polarized family are trivial.
This separates action representability from the proved arithmetic rigidity. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s N : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N M.left)

theorem relativePELUniversal_classifying_unique
    {T Z : Over M.left} (u : (ActionFunctor.relativePELActionFunctor P iotaO M A).obj (op Z))
    (hclass : Function.Injective (fun f : T ⟶ Z => (ActionFunctor.relativePELActionFunctor P iotaO M A).map f.op u))
    (hRigid : ∀ e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (A.pullback T.hom),
      e.abelian.hom = 𝟙 (A.abelian.pullback T.hom).scheme)
    (f g : T ⟶ Z)
    (e : PEL.Iso.PolarizedActionIso
      ((FamilyClassification.relativePELUniversal P iotaO M A Z u).data.pullback f.left)
      ((FamilyClassification.relativePELUniversal P iotaO M A Z u).data.pullback g.left)) : f = g := by
  let a := (FamilyClassification.relativePELUniversal_restrictionIso P iotaO M A u f).symm.trans
    (e.trans (FamilyClassification.relativePELUniversal_restrictionIso P iotaO M A u g))
  have ha := hRigid a.polarized
  apply hclass
  apply Subtype.ext
  apply Integral.ActionScheme.ringHomOfIntegralAction_injective
  apply RingHom.ext
  intro x
  apply Finite.Actions.GroupEndRing.ext
  have hx := a.action x
  change ((ActionFunctor.relativePELActionFunctor P iotaO M A).map f.op u).val.map x ≫ a.polarized.abelian.hom =
    a.polarized.abelian.hom ≫ ((ActionFunctor.relativePELActionFunctor P iotaO M A).map g.op u).val.map x at hx
  rw [ha] at hx
  exact (Category.comp_id _).symm.trans (hx.trans (Category.id_comp _))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FamilyUniqueness
