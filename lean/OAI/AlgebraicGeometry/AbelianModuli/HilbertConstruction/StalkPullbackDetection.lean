import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReducedFieldPullbackDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.PullbackMapEquality
import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Stalk Pullback Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StalkPullbackDetection

noncomputable section

/-! Morphisms with locally noetherian source are detected by base changes to every local ring of the base scheme, including nonreduced local rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem overHom_eq_of_stalkPullbacks {S : Scheme.{u}} {A B : Over S}
    [IsLocallyNoetherian A.left] (f g : A ⟶ B)
    (h : ∀ x : S, (Over.pullback (S.fromSpecStalk x)).map f =
      (Over.pullback (S.fromSpecStalk x)).map g) : f = g := by
  apply Over.OverMorphism.ext
  apply Scheme.hom_ext_of_forall
  intro x
  apply spread_out_unique_of_isGermInjective' f.left g.left
  let r := A.left.fromSpecStalk x
  let b := S.fromSpecStalk (A.hom x)
  let a := Spec.map (A.hom.stalkMap x)
  have hr : r ≫ A.hom = a ≫ b := (Scheme.SpecMap_stalkMap_fromSpecStalk A.hom).symm
  have hp : (Over.pullback (a ≫ b)).map f = (Over.pullback (a ≫ b)).map g :=
    (Iterated.PullbackMapEquality.overPullback_map_eq_iff_iterated a b f g).mpr (congrArg (Over.pullback a).map (h (A.hom x)))
  exact ReducedFieldPullbackDetection.overHom_point_eq_of_pullback_eq (a ≫ b) r hr f g hp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StalkPullbackDetection
