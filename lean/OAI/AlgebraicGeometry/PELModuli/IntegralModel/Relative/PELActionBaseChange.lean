import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.IntegralActionBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ActionFunctor
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.RosatiRestriction

/-! # PEL Action Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.PELActionBaseChange

noncomputable section

/-! Changing the base of the relative PEL-action functor preserves and
reflects its literal Rosati and arithmetic Lie-rank predicates. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

namespace ActionBaseChange
variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s N : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N M.left)
    {B : Scheme.{0}} (b : B ⟶ M.left)

theorem rosati_iff (T : Over B)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) ((A.pullback b).pullback T.hom).abelian) :
    AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation ((A.pullback b).pullback T.hom) ρ ↔
      AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback ((Over.map b).obj T).hom)
        (Integral.IntegralActionBaseChange.ActionBaseChange.actionEquiv A.abelian b T ρ) := by
  apply RosatiRestriction.rosati_iff_of_polarized_iso (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A b T.hom) ρ _
  intro a
  change (ActionBaseChangeComparison.ActionBaseChange.groupIso A.abelian b T).hom ≫
      ((ActionBaseChangeComparison.ActionBaseChange.groupIso A.abelian b T).inv ≫ ρ.map a ≫ (ActionBaseChangeComparison.ActionBaseChange.groupIso A.abelian b T).hom) =
    ρ.map a ≫ (ActionBaseChangeComparison.ActionBaseChange.groupIso A.abelian b T).hom
  exact Iso.hom_inv_id_assoc _ _

omit [NumberField E] [NumberField.IsCMField E] in
theorem lieRanks_iff (T : Over B)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) ((A.pullback b).pullback T.hom).abelian) :
    PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map (b ≫ M.hom)).obj T)
      ((A.abelian.pullback b).pullback T.hom) ρ ↔
    PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map M.hom).obj ((Over.map b).obj T))
      (A.abelian.pullback ((Over.map b).obj T).hom) (Integral.IntegralActionBaseChange.ActionBaseChange.actionEquiv A.abelian b T ρ) := by
  change PEL.Has.HasIntegralLieRanks P R iotaO (Over.mk (T.hom ≫ (b ≫ M.hom))) _ ρ ↔ _
  rw [← Category.assoc T.hom b M.hom]
  apply Integral.LieRankRestriction.integralLieRanks_iff_of_iso P iotaO (Over.mk ((T.hom ≫ b) ≫ M.hom))
    ρ (Integral.IntegralActionBaseChange.ActionBaseChange.actionEquiv A.abelian b T ρ) (ActionBaseChangeComparison.ActionBaseChange.groupIso A.abelian b T)
  intro a
  change ρ.map a ≫ (ActionBaseChangeComparison.ActionBaseChange.groupIso A.abelian b T).hom =
    (ActionBaseChangeComparison.ActionBaseChange.groupIso A.abelian b T).hom ≫
      ((ActionBaseChangeComparison.ActionBaseChange.groupIso A.abelian b T).inv ≫ ρ.map a ≫ (ActionBaseChangeComparison.ActionBaseChange.groupIso A.abelian b T).hom)
  exact (Iso.hom_inv_id_assoc _ _).symm

def pelEquiv (T : Over B) :
    (ActionFunctor.relativePELActionFunctor P iotaO (Over.mk (b ≫ M.hom)) (A.pullback b)).obj (op T) ≃
      (ActionFunctor.relativePELActionFunctor P iotaO M A).obj (op ((Over.map b).obj T)) :=
  Equiv.subtypeEquiv (Integral.IntegralActionBaseChange.ActionBaseChange.actionEquiv A.abelian b T) (fun ρ =>
    and_congr (rosati_iff P M A b T ρ) (lieRanks_iff P iotaO M A b T ρ))

def relativePELActionFunctorIso :
    ActionFunctor.relativePELActionFunctor P iotaO (Over.mk (b ≫ M.hom)) (A.pullback b) ≅
      (Over.map b).op ⋙ ActionFunctor.relativePELActionFunctor P iotaO M A :=
  NatIso.ofComponents (fun T => (pelEquiv P iotaO M A b T.unop).toIso) (by
    intro T U f
    apply ConcreteCategory.hom_ext
    intro ρ
    apply Subtype.ext
    exact Integral.IntegralActionBaseChange.ActionBaseChange.actionEquiv_natural A.abelian b f.unop ρ.val)

end ActionBaseChange

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.PELActionBaseChange
