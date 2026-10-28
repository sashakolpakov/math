import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.NeutralRowFrame
import OAI.AlgebraicGeometry.Picard.PoincareBundle.SymmetryTransportedFrames

/-! # Origin Frame Comparison -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.OriginFrameComparison

noncomputable section

/-! Isotropy identifies the first kernel frame at the origin with a frame defined over the whole abelian scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionFrames

theorem isotropic_values_at {S : Scheme.{u}} {H K A B : Over S} (i : H ⟶ A) (j : K ⟶ B)
    (Q : Line.Bundles.LineBundle (A ⊗ B).left)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ B).left ≅ (Scheme.Modules.pullback (i ⊗ₘ 𝟙 B).left).obj Q.sheaf)
    (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (A ⊗ K).left ≅ (Scheme.Modules.pullback (𝟙 A ⊗ₘ j).left).obj Q.sheaf)
    (hi : ∀ (T : Over S) (a : T ⟶ H) (b : T ⟶ K), Kernel.IntersectionFrames.obstruction i j Q s t a b = 1)
    {T : Over S} (a : T ⟶ H) (b : T ⟶ K)
    (u : T ⟶ H ⊗ B) (v : T ⟶ A ⊗ K) (x : T ⟶ A ⊗ B)
    (hu : lift a (b ≫ j) = u) (hv : lift (a ≫ i) b = v) (hx : lift (a ≫ i) (b ≫ j) = x)
    (hup : u ≫ (i ⊗ₘ 𝟙 B) = x) (hvq : v ≫ (𝟙 A ⊗ₘ j) = x) :
    GlobalPullbackFrame.atPoint (i ⊗ₘ 𝟙 B) Q s u x hup =
      GlobalPullbackFrame.atPoint (𝟙 A ⊗ₘ j) Q t v x hvq := by
  subst u
  subst v
  subst x
  exact IntersectionFrameValues.isotropic_values i j Q s t hi a b

variable {S : Scheme.{u}} {H A : Over S} [GrpObj H] [GrpObj A] (i : H ⟶ A) [IsMonHom i]
  (Q : Line.Bundles.LineBundle (A ⊗ A).left)
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ A).left ≅ (Scheme.Modules.pullback (i ⊗ₘ 𝟙 A).left).obj Q.sheaf)
  (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (A ⊗ H).left ≅ (Scheme.Modules.pullback (𝟙 A ⊗ₘ i).left).obj Q.sheaf)

omit [GrpObj H] [IsMonHom i] in
theorem first_origin_square {T : Over S} (a : T ⟶ H) :
    lift a (1 : T ⟶ A) ≫ (i ⊗ₘ 𝟙 A) = lift (a ≫ i) (1 : T ⟶ A) := by
  rw [lift_map, Category.comp_id]

/-- The origin frame comes by restriction from the neutral row on the whole original scheme. -/
theorem origin_frame
    (hi : ∀ (T : Over S) (a b : T ⟶ H), Kernel.IntersectionFrames.obstruction i i Q s t a b = 1)
    {T : Over S} (a : T ⟶ H) :
    GlobalPullbackFrame.atPoint (i ⊗ₘ 𝟙 A) Q s (lift a (1 : T ⟶ A))
        (lift (a ≫ i) (1 : T ⟶ A)) (first_origin_square i a) =
      GlobalPullbackFrame.atPoint (lift (𝟙 A) (1 : A ⟶ A)) Q
        (Kernel.NeutralRowFrame.frame i Q t) (a ≫ i) (lift (a ≫ i) (1 : T ⟶ A))
        (Kernel.NeutralRowFrame.row_point (a ≫ i)) := by
  have hu : lift a ((1 : T ⟶ H) ≫ i) = lift a (1 : T ⟶ A) := by rw [MonObj.one_comp]
  have hx : lift (a ≫ i) ((1 : T ⟶ H) ≫ i) = lift (a ≫ i) (1 : T ⟶ A) := by rw [MonObj.one_comp]
  have hp := isotropic_values_at i i Q s t hi a (1 : T ⟶ H) (lift a (1 : T ⟶ A))
    (lift (a ≫ i) (1 : T ⟶ H)) (lift (a ≫ i) (1 : T ⟶ A)) hu rfl hx
    (first_origin_square i a) (Kernel.NeutralRowFrame.point_square i (a ≫ i))
  have hr := Kernel.NeutralRowFrame.evaluation i Q t (a ≫ i)
  have he := SymmetryTransportedFrames.evaluation_eq (lift (𝟙 A) (1 : A ⟶ A)) Q
    (Kernel.NeutralRowFrame.frame i Q t) (a ≫ i) (lift (a ≫ i) (1 : T ⟶ A))
    (Kernel.NeutralRowFrame.row_point (a ≫ i))
  exact hp.trans (hr.symm.trans he.symm)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.OriginFrameComparison
