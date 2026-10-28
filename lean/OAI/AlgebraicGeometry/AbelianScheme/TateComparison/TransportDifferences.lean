import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldPointTransport

/-! # Transport Differences -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TransportDifferences

noncomputable section

/-! A difference equation over an extension has an exact expression on
points over the original field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S S' T : Scheme.{u}} (p : S' ⟶ S) (c : T ⟶ S') (b : T ⟶ S)
  (h : c ≫ p = b)

theorem pointBaseChangeEnd_differences (A X : Over S) [GrpObj A]
    (φ : (Over.pullback p).obj A ⟶ (Over.pullback p).obj A) [IsMonHom φ]
    (f g : X ⟶ A)
    (hf : ∀ (x y : Over.mk c ⟶ (Over.pullback p).obj X),
      ((x ≫ (Over.pullback p).map f) / (y ≫ (Over.pullback p).map f)) ≫ φ =
        (x ≫ (Over.pullback p).map g) / (y ≫ (Over.pullback p).map g))
    (x y : Over.mk b ⟶ X) :
    FieldPointTransport.pointBaseChangeEnd p c b h A φ (Additive.ofMul ((x ≫ f) / (y ≫ f))) =
      Additive.ofMul ((x ≫ g) / (y ≫ g)) := by
  let x' := (FieldPointTransport.pointBaseChangeEquiv p c b h X).symm x
  let y' := (FieldPointTransport.pointBaseChangeEquiv p c b h X).symm y
  have he (a : X ⟶ A) :
      FieldPointTransport.pointBaseChangeMulEquiv p c b h A
        ((x' ≫ (Over.pullback p).map a) / (y' ≫ (Over.pullback p).map a)) =
          (x ≫ a) / (y ≫ a) := by
    rw [map_div, FieldPointTransport.pointBaseChange_comp, FieldPointTransport.pointBaseChange_comp]
    simp only [x', y', Equiv.apply_symm_apply]
  rw [← he f, FieldPointTransport.pointBaseChangeEnd_apply, hf, he g]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TransportDifferences
