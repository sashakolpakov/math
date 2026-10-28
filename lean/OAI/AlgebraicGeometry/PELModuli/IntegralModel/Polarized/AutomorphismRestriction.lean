import OAI.AlgebraicGeometry.PELModuli.IntegralModel.RosatiRestriction

/-! # Automorphism Restriction -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismRestriction

noncomputable section

/-! Geometric restriction of a polarized automorphism agrees with the
actual endomorphism-family restriction, including its group law. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) {T U : Over S}

def restrictPolarizedAutomorphism (f : T ⟶ U)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback U.hom) (A.pullback U.hom)) :
    AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (A.pullback T.hom) :=
  (RosatiRestriction.polarizedRestrictionIso A f).symm.trans ((e.pullback f.left).trans (RosatiRestriction.polarizedRestrictionIso A f))

theorem restrictPolarizedAutomorphism_hom (f : T ⟶ U)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback U.hom) (A.pullback U.hom)) :
    (restrictPolarizedAutomorphism A f e).abelian.hom =
      (EndomorphismFamiliesId.EndomorphismFamilies.restrict A.abelian f (Finite.Actions.GroupEndRing.ofHom (A.abelian.pullback U.hom) e.abelian.hom)).hom
        (A.abelian.pullback T.hom) := by
  change (RosatiRestriction.polarizedRestrictionIso A f).abelian.inv ≫
    (Over.pullback f.left).map e.abelian.hom ≫ (RosatiRestriction.polarizedRestrictionIso A f).abelian.hom = _
  rw [RosatiRestriction.polarizedRestrictionIso_abelian]
  rfl

def liftPolarizedAutomorphism (f : T ⟶ U)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (A.pullback T.hom)) :
    AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso ((A.pullback U.hom).pullback f.left) ((A.pullback U.hom).pullback f.left) :=
  (RosatiRestriction.polarizedRestrictionIso A f).trans (e.trans (RosatiRestriction.polarizedRestrictionIso A f).symm)

theorem liftPolarizedAutomorphism_hom (f : T ⟶ U)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (A.pullback T.hom))
    (r : Finite.Actions.GroupEndRing (A.abelian.pullback U.hom))
    (hr : EndomorphismFamiliesId.EndomorphismFamilies.restrict A.abelian f r = Finite.Actions.GroupEndRing.ofHom _ e.abelian.hom) :
    (liftPolarizedAutomorphism A f e).abelian.hom = (Over.pullback f.left).map (r.hom _) := by
  have h : (RosatiRestriction.polarizedRestrictionIso A f).abelian.inv ≫ (Over.pullback f.left).map (r.hom _) ≫
      (RosatiRestriction.polarizedRestrictionIso A f).abelian.hom = e.abelian.hom := by
    rw [RosatiRestriction.polarizedRestrictionIso_abelian]
    exact congrArg (Finite.Actions.GroupEndRing.hom (A.abelian.pullback T.hom)) hr
  have h' := congrArg (fun m => (RosatiRestriction.polarizedRestrictionIso A f).abelian.hom ≫ m ≫
    (RosatiRestriction.polarizedRestrictionIso A f).abelian.inv) h
  change (RosatiRestriction.polarizedRestrictionIso A f).abelian.hom ≫ e.abelian.hom ≫
    (RosatiRestriction.polarizedRestrictionIso A f).abelian.inv = (Over.pullback f.left).map (r.hom _)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using h'.symm

def flattenPolarizedAutomorphism (f : T ⟶ U)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso ((A.pullback U.hom).pullback f.left) ((A.pullback U.hom).pullback f.left)) :
    AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (A.pullback T.hom) :=
  (RosatiRestriction.polarizedRestrictionIso A f).symm.trans (e.trans (RosatiRestriction.polarizedRestrictionIso A f))

theorem flattenPolarizedAutomorphism_hom (f : T ⟶ U)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso ((A.pullback U.hom).pullback f.left) ((A.pullback U.hom).pullback f.left))
    (r : Finite.Actions.GroupEndRing (A.abelian.pullback U.hom))
    (hr : e.abelian.hom = (Over.pullback f.left).map (r.hom _)) :
    (flattenPolarizedAutomorphism A f e).abelian.hom =
      (EndomorphismFamiliesId.EndomorphismFamilies.restrict A.abelian f r).hom (A.abelian.pullback T.hom) := by
  change (RosatiRestriction.polarizedRestrictionIso A f).abelian.inv ≫ e.abelian.hom ≫
    (RosatiRestriction.polarizedRestrictionIso A f).abelian.hom = _
  rw [hr, RosatiRestriction.polarizedRestrictionIso_abelian]
  rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismRestriction
