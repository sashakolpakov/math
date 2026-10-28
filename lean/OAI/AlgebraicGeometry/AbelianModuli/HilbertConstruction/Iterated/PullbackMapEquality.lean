import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Pullback Map Equality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.PullbackMapEquality

noncomputable section

/-! Equality after a composite base change is equivalent to equality after the corresponding iterated pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem overPullback_map_eq_iff_iterated {S T U : Scheme.{u}} {A B : Over S}
    (s : U ⟶ T) (t : T ⟶ S) (f q : A ⟶ B) :
    (Over.pullback (s ≫ t)).map f = (Over.pullback (s ≫ t)).map q ↔
      (Over.pullback s).map ((Over.pullback t).map f) =
        (Over.pullback s).map ((Over.pullback t).map q) := by
  let e := Over.pullbackComp s t
  constructor
  · intro h
    apply (cancel_epi (e.hom.app A)).mp
    exact (e.hom.naturality f).symm.trans ((congrArg (fun v => v ≫ e.hom.app B) h).trans
      (e.hom.naturality q))
  · intro h
    apply (cancel_mono (e.hom.app B)).mp
    exact (e.hom.naturality f).trans ((congrArg (fun v => e.hom.app A ≫ v) h).trans
      (e.hom.naturality q).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.PullbackMapEquality
