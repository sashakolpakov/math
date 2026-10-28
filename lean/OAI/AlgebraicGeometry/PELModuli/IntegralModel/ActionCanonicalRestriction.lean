import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.IntegralActionBaseChange

/-! # Action Canonical Restriction -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ActionCanonicalRestriction

noncomputable section

/-! The canonical base-change action equivalence agrees with restriction
along the actual structural map of each test over the new base. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace ActionBaseChange
variable {S B : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (b : B ⟶ S)

def testInclusion (T : Over B) : (Over.map b).obj T ⟶ Over.mk b := Over.homMk T.hom rfl

theorem canonicalRestrictionIso (T : Over B) :
    EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A (testInclusion b T) = ActionBaseChangeComparison.ActionBaseChange.groupIso A b T := by
  simp only [EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso, testInclusion,
    Over.mk_hom, Over.map_obj_hom, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCongrIso,
    eqToIso_refl, Iso.trans_refl, ActionBaseChangeComparison.ActionBaseChange.groupIso]
  rfl

theorem actionEquiv_pullback {R : Type} [CommRing R] (T : Over B)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R (A.pullback b)) :
    Integral.ActionScheme.restrictIntegralAction A ρ (testInclusion b T) = Integral.IntegralActionBaseChange.ActionBaseChange.actionEquiv A b T (ρ.pullback T.hom) := by
  apply Finite.Actions.integralAction_ext
  intro a
  change (EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A (testInclusion b T)).inv ≫
      (Over.pullback T.hom).map (ρ.map a) ≫
        (EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A (testInclusion b T)).hom =
    (ActionBaseChangeComparison.ActionBaseChange.groupIso A b T).inv ≫ (Over.pullback T.hom).map (ρ.map a) ≫ (ActionBaseChangeComparison.ActionBaseChange.groupIso A b T).hom
  rw [canonicalRestrictionIso]

end ActionBaseChange

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ActionCanonicalRestriction
