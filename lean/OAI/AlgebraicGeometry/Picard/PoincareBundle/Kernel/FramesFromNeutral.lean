import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationCoordinateMap
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

/-! # Frames From Neutral -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesFromNeutral

noncomputable section

/-!
# Construct multiplicative kernel frames from normalized neutral fibers and scheme-theoretic annihilation

The neutral-fiber product condition is an ordinary normalization of the line multiplication,
independent of the subgroup. It holds for the actual pulled-back product by
`NeutralFiberProducts.pullback_unitFrame_product`.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationCoordinateMap

variable {S : Scheme.{u}} {E A B Z X : Over S} [GrpObj A] [GrpObj B] [GrpObj Z]
  (p : E ⟶ A) (r : E ⟶ X) (f : A ⟶ B) [IsMonHom f]
  (φ : A ⟶ Z) [IsMonHom φ] (hφ : Kernel.Scheme.kernelInclusion f ≫ φ = 1)

include hφ in
omit [GrpObj A] [IsMonHom f] [IsMonHom φ] in
/-- The actual group coordinate of every represented kernel point maps to the neutral coordinate. -/
theorem kernel_point_neutral {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (a : T ⟶ E)
    (ha : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ p) : a ≫ (p ≫ φ) = 1 := by
  rw [← Category.assoc, ← ha, Category.assoc, hφ, MonObj.comp_one]

variable (L : Line.Bundles.LineBundle E.left) (D : FiberwiseMultiplication.Multiplication (p ≫ φ) r L)
  (hunit : ∀ (T : Over S) (a b c : T ⟶ E)
    (ha : a ≫ (p ≫ φ) = 1) (hb : b ≫ (p ≫ φ) = 1) (hc : c ≫ (p ≫ φ) = 1)
    (h : FiberwiseMultiplication.ProductRel (p ≫ φ) r a b c) (U : T.left.Opens),
    (D.product a b c h).app U ((D.unitFrame a ha).hom.app U (1 : Γ(T.left, U)))
      ((D.unitFrame b hb).hom.app U (1 : Γ(T.left, U))) = (D.unitFrame c hc).hom.app U (1 : Γ(T.left, U)))

attribute [local instance] Kernel.Scheme.kernelGroup

/-- The normalized neutral frames give genuine multiplicative kernel frames, with all laws proved. -/
def kernelFrames : FiberwiseMultiplication.KernelFrames p r L f (MultiplicationCoordinateMap.restrictCoordinate p r φ L D) where
  frame := fun {_T} k a ha => D.unitFrame a (kernel_point_neutral p f φ hφ k a ha)
  unit := fun {_T} _a _ha _hk => rfl
  multiplicative := fun {T} k l m _hm a b c ha hb hc hab U =>
    hunit T a b c (kernel_point_neutral p f φ hφ k a ha) (kernel_point_neutral p f φ hφ l b hb)
      (kernel_point_neutral p f φ hφ m c hc) (MultiplicationCoordinateMap.mappedRel p r φ a b c hab) U
  natural := fun {_T _T'} g k k' _hgk a a' ha ha' hga =>
    D.unit_natural g a a' (kernel_point_neutral p f φ hφ k a ha)
      (kernel_point_neutral p f φ hφ k' a' ha') hga

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesFromNeutral
