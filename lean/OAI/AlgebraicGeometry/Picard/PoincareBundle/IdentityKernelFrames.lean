import OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.FiberProducts
import OAI.AlgebraicGeometry.Picard.PoincareBundle.TransverseNeutralPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport

/-! # Identity Kernel Frames -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.IdentityKernelFrames

noncomputable section

/-! The identity quotient's actual kernel frames are the normalized unit fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

attribute [local instance] Kernel.Scheme.kernelGroup

variable {S : Scheme.{u}} {E A X : Over S} [GrpObj A]
  (p : E ⟶ A) (r : E ⟶ X) [Mono (lift p r)]
  (L : Line.Bundles.LineBundle E.left) (D : FiberwiseMultiplication.Multiplication p r L)

omit [Mono (lift p r)] in
/-- A point in the actual identity kernel has neutral group coordinate. -/
theorem coordinate_one {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject (𝟙 A)) (a : T ⟶ E)
    (ha : k ≫ Kernel.Scheme.kernelInclusion (𝟙 A) = a ≫ p) : a ≫ p = 1 := by
  have h := (Kernel.Scheme.kernelPointsEquiv (𝟙 A) T k).property
  change (k ≫ Kernel.Scheme.kernelInclusion (𝟙 A)) ≫ 𝟙 A = 1 at h
  rw [Category.comp_id] at h
  exact ha.symm.trans h

/-- The full multiplicative natural frame system comes directly from the actual unit frames. -/
def frames : FiberwiseMultiplication.KernelFrames p r L (𝟙 A) D where
  frame := fun {_T} k a ha => D.unitFrame a (coordinate_one p k a ha)
  unit := fun {_T} _a _ha _hk => rfl
  multiplicative := fun {_T} k l t _hkt a b c ha hb hc hab U =>
    Neutral.FiberProducts.unitFrame_product p r L D a b c
      (coordinate_one p k a ha) (coordinate_one p l b hb) (coordinate_one p t c hc) hab U
  natural := fun {_T _U} u k k' _huk a a' ha ha' hua =>
    D.unit_natural u a a' (coordinate_one p k a ha) (coordinate_one p k' a' ha') hua

variable [GrpObj X] (Dv : FiberwiseMultiplication.Multiplication r p L)
  (ht : TransverseNeutralPullback.TransverseUnits D Dv)

include ht

/-- The original transverse unit law supplies transversality of the identity-kernel frame system. -/
theorem transverse : Kernel.FramesTransverseTransport.Transverse (𝟙 A) (frames p r L D) Dv := by
  intro T k a b c ha hb hc h U
  exact ht T a b c (coordinate_one p k a ha) (coordinate_one p k b hb) (coordinate_one p k c hc) h U

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.IdentityKernelFrames
