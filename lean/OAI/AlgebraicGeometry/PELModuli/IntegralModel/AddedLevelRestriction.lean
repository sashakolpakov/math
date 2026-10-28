import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismRestriction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AddedLevelRelabeling

/-! # Added Level Restriction -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.AddedLevelRestriction

noncomputable section

/-! The canonical relative-family comparison preserves both ordered
levels. Its auxiliary component is the same comparison used by the
integral PEL action classifier. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

def addedLevelRestrictionIso {S : Scheme.{0}} {g L N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel g δ L N S) {T U : Over S} (f : T ⟶ U) :
    AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel.Iso ((A.pullback U.hom).pullback f.left) (A.pullback T.hom) where
  auxiliary := RosatiRestriction.polarizedRestrictionIso A.auxiliary f
  prescribed := by
    apply AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
    intro V c
    have h := A.prescribed.restrict_pullback f
    have hb := congrArg (fun β : (A.auxiliary.abelian.pullback T.hom).FullLevel N =>
      (β.hom.app (.op V) c).val) h
    change (((A.prescribed.pullback U.hom).pullback f.left).hom.app (.op V) c).val ≫
      (RosatiRestriction.polarizedRestrictionIso A.auxiliary f).abelian.hom = _
    rw [RosatiRestriction.polarizedRestrictionIso_abelian]
    exact (Category.assoc _ _ _).symm.trans hb

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.AddedLevelRestriction
