import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Ring.Equiv

/-! # Unit Map Conjugation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UnitMapConjugation

/-! Units commute with conjugating an actual section-ring map
through a ring equivalence. -/

theorem units_map_conjugate {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (f : R →+* R) (u : Rˣ) :
    Units.map e.toMonoidHom (Units.map f.toMonoidHom u) =
      Units.map (e.toRingHom.comp (f.comp e.symm.toRingHom)).toMonoidHom (Units.map e.toMonoidHom u) := by
  apply Units.ext
  change e (f u.val) = e (f (e.symm (e u.val)))
  rw [e.symm_apply_apply]

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UnitMapConjugation
