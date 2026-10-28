import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.UnitSubgroup

/-! # Automorphism Identity Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The unit value detects the identity polarized automorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable {A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S}

theorem Moduli.Isomorphisms.LevelPreservingIso.eq_refl_of_endRingUnit_eq_one (e : Moduli.Isomorphisms.LevelPreservingIso A A)
    (he : e.endRingUnit.val = 1) : e = Moduli.Isomorphisms.LevelPreservingIso.refl A :=
  Moduli.Isomorphisms.LevelPreservingIso.ext_abelian e (Moduli.Isomorphisms.LevelPreservingIso.refl A)
    (congrArg (fun f : A.abelian.EndRing => f.toMul.hom.hom) he)

theorem Moduli.Isomorphisms.LevelPreservingIso.automorphismUnit_refl : (Moduli.Isomorphisms.LevelPreservingIso.refl A).automorphismUnit = 1 :=
  Subtype.ext Moduli.Isomorphisms.LevelPreservingIso.endRingUnit_refl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
