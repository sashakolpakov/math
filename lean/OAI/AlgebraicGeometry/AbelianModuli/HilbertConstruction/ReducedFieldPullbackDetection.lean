import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Reduced Field Pullback Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReducedFieldPullbackDetection

noncomputable section

/-! Maps from a reduced relative scheme to a separated relative scheme are determined by all field-valued base changes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {A B : Over S}

theorem overHom_point_eq_of_pullback_eq {T : Scheme.{u}} (b : T ⟶ S)
    (r : T ⟶ A.left) (hr : r ≫ A.hom = b) (f g : A ⟶ B)
    (h : (Over.pullback b).map f = (Over.pullback b).map g) : r ≫ f.left = r ≫ g.left := by
  let a : T ⟶ Limits.pullback A.hom b := Limits.pullback.lift r (𝟙 T)
    (hr.trans (Category.id_comp b).symm)
  have ha : a ≫ Limits.pullback.fst A.hom b = r := Limits.pullback.lift_fst _ _ _
  have H : Limits.pullback.fst A.hom b ≫ f.left = Limits.pullback.fst A.hom b ≫ g.left :=
    (Pullback.Comparisons.overPullback_map_left_fst f b).symm.trans
      ((congrArg (fun p : (Over.pullback b).obj A ⟶ (Over.pullback b).obj B =>
        p.left ≫ Limits.pullback.fst B.hom b) h).trans (Pullback.Comparisons.overPullback_map_left_fst g b))
  have H' := congrArg (fun p : Limits.pullback A.hom b ⟶ B.left => a ≫ p) H
  simpa only [← Category.assoc, ha] using H'

variable [IsReduced A.left] [IsSeparated B.hom]

theorem overHom_eq_of_fieldPullbacks_of_reduced (f g : A ⟶ B)
    (h : ∀ (K : Type u) [Field K] (b : Spec (.of K) ⟶ S),
      (Over.pullback b).map f = (Over.pullback b).map g) : f = g := by
  apply Over.OverMorphism.ext
  apply ext_of_fromSpecResidueField_eq f.left g.left B.hom Set.univ dense_univ
  · intro x _
    let r := A.left.fromSpecResidueField x
    let b := r ≫ A.hom
    exact overHom_point_eq_of_pullback_eq b r rfl f g (h (A.left.residueField x) b)
  · exact f.w.trans g.w.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReducedFieldPullbackDetection
