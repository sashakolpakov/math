import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.GlobalDegree

/-! # Torsion Degree -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The full-level torsion scheme has rank equal to the cardinality of the ordered standard module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {g n : ℕ} [NeZero n] (A : Abelian.Schemes.AbelianScheme g S)

theorem Abelian.Schemes.AbelianScheme.fullLevel_torsion_finrank (level : A.FullLevel n) (s : S) :
    (A.torsionScheme n).hom.finrank s = n ^ (2 * g) := by
  let I := ULift.{u} (Multiplicative (Fin (2 * g) → ZMod n))
  let e := level.schemeIso
  have := level.torsion_etale
  have := level.torsion_finite
  have : IsIso e.hom.left := inferInstanceAs (IsIso (((Over.forget S).mapIso e).hom))
  have he : (Level.Scheme.constantFullLevelScheme g n S).hom.finrank s = (A.torsionScheme n).hom.finrank s :=
    (congrArg (fun f : (Level.Scheme.constantFullLevelScheme g n S).left ⟶ S => f.finrank s)
      e.hom.w.symm).trans
      (congrFun (Scheme.Hom.finrank_comp_left_of_isIso e.hom.left (A.torsionScheme n).hom) s)
  have hc : (Level.Scheme.constantFullLevelScheme g n S).hom.finrank s = n ^ (2 * g) :=
    (ConstantScheme.GlobalDegree.constantScheme_finrank I s).trans (by simp [I])
  exact he.symm.trans hc

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
