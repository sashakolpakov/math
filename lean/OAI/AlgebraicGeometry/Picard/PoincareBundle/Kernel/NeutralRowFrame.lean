import OAI.AlgebraicGeometry.Picard.PoincareBundle.IntersectionFrameValues

/-! # Neutral Row Frame -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.NeutralRowFrame

noncomputable section

/-! Restrict the second kernel frame to the neutral subgroup point over the whole abelian scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioPullback

variable {S : Scheme.{u}} {H A : Over S} [GrpObj H] [GrpObj A] (i : H ⟶ A) [IsMonHom i]
  (Q : Line.Bundles.LineBundle (A ⊗ A).left)
  (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (A ⊗ H).left ≅ (Scheme.Modules.pullback (𝟙 A ⊗ₘ i).left).obj Q.sheaf)

theorem neutral_square : lift (𝟙 A) (1 : A ⟶ H) ≫ (𝟙 A ⊗ₘ i) = lift (𝟙 A) (1 : A ⟶ A) := by
  rw [lift_map, Category.comp_id, MonObj.one_comp]

/-- A global Poincare frame along the entire neutral row, constructed from the second kernel frame. -/
def frame : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ≅ Line.Fibers.fiber Q (lift (𝟙 A) (1 : A ⟶ A)) :=
  GlobalPullbackFrame.atPoint (𝟙 A ⊗ₘ i) Q t (lift (𝟙 A) (1 : A ⟶ H))
    (lift (𝟙 A) (1 : A ⟶ A)) (neutral_square i)

theorem point_square {T : Over S} (x : T ⟶ A) :
    lift x (1 : T ⟶ H) ≫ (𝟙 A ⊗ₘ i) = lift x (1 : T ⟶ A) := by
  rw [lift_map, Category.comp_id, MonObj.one_comp]

theorem row_point {T : Over S} (x : T ⟶ A) :
    x ≫ lift (𝟙 A) (1 : A ⟶ A) = lift x (1 : T ⟶ A) := by
  rw [comp_lift, Category.comp_id, MonObj.comp_one]

/-- The neutral row frame recovers the original second frame at every base-valued point. -/
theorem evaluation {T : Over S} (x : T ⟶ A) :
    FrameRatioPullback.pullFrame x.left (frame i Q t) ≪≫
        Line.Fibers.fiberPullbackIso Q x (lift (𝟙 A) (1 : A ⟶ A)) (lift x (1 : T ⟶ A)) (row_point x) =
      GlobalPullbackFrame.atPoint (𝟙 A ⊗ₘ i) Q t (lift x (1 : T ⟶ H))
        (lift x (1 : T ⟶ A)) (point_square i x) := by
  have hx : x ≫ lift (𝟙 A) (1 : A ⟶ H) = lift x (1 : T ⟶ H) := by
    rw [comp_lift, Category.comp_id, MonObj.comp_one]
  exact GlobalFrameNaturality.atPoint_pullback (𝟙 A ⊗ₘ i) Q t x
    (lift (𝟙 A) (1 : A ⟶ H)) (lift (𝟙 A) (1 : A ⟶ A)) (neutral_square i)
    (lift x (1 : T ⟶ H)) (lift x (1 : T ⟶ A)) (point_square i x) hx (row_point x)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.NeutralRowFrame
