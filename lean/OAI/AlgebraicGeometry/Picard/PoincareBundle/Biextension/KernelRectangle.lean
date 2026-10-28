import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData

/-! # Kernel Rectangle -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.KernelRectangle

noncomputable section

/-!
# Actual kernel-intersection coordinates in a biextension translation rectangle
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseKernelCoordinates OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData

variable {S : Scheme.{u}} {A B X Y : Over S} [GrpObj B] [GrpObj Y]
  (f : A ⟶ B) (g : X ⟶ Y)

/-- The actual point where the two kernel directions cross. -/
def crossPoint {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (l : T ⟶ Kernel.Scheme.kernelObject g) : T ⟶ A ⊗ X :=
  lift (k ≫ Kernel.Scheme.kernelInclusion f) (l ≫ Kernel.Scheme.kernelInclusion g)

theorem crossPoint_fst {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (l : T ⟶ Kernel.Scheme.kernelObject g) :
    crossPoint f g k l ≫ fst A X = k ≫ Kernel.Scheme.kernelInclusion f := lift_fst _ _

theorem crossPoint_snd {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (l : T ⟶ Kernel.Scheme.kernelObject g) :
    crossPoint f g k l ≫ snd A X = l ≫ Kernel.Scheme.kernelInclusion g := lift_snd _ _

theorem horizontalPoint_fst {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (x : T ⟶ A ⊗ X) :
    FiberwiseKernelCoordinates.kernelPoint f AxisData.replaceFirst k x ≫ fst A X = k ≫ Kernel.Scheme.kernelInclusion f :=
  FiberwiseKernelCoordinates.kernelPoint_group (fst A X) f AxisData.replaceFirst AxisData.replaceFirst_group k x

theorem horizontalPoint_snd {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (x : T ⟶ A ⊗ X) :
    FiberwiseKernelCoordinates.kernelPoint f AxisData.replaceFirst k x ≫ snd A X = x ≫ snd A X :=
  FiberwiseKernelCoordinates.kernelPoint_base (snd A X) f AxisData.replaceFirst AxisData.replaceFirst_base k x

theorem verticalPoint_fst {T : Over S} (l : T ⟶ Kernel.Scheme.kernelObject g) (x : T ⟶ A ⊗ X) :
    FiberwiseKernelCoordinates.kernelPoint g AxisData.replaceSecond l x ≫ fst A X = x ≫ fst A X :=
  FiberwiseKernelCoordinates.kernelPoint_base (fst A X) g AxisData.replaceSecond AxisData.replaceSecond_base l x

theorem verticalPoint_snd {T : Over S} (l : T ⟶ Kernel.Scheme.kernelObject g) (x : T ⟶ A ⊗ X) :
    FiberwiseKernelCoordinates.kernelPoint g AxisData.replaceSecond l x ≫ snd A X = l ≫ Kernel.Scheme.kernelInclusion g :=
  FiberwiseKernelCoordinates.kernelPoint_group (snd A X) g AxisData.replaceSecond AxisData.replaceSecond_group l x

variable [GrpObj A] [IsCommMonObj A]

/-- The horizontal product of the crossing fiber and vertical kernel fiber is the translated vertical fiber. -/
theorem horizontalCross_product {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (l : T ⟶ Kernel.Scheme.kernelObject g)
    (x y : T ⟶ A ⊗ X) (h : (x ≫ fst A X) * (k ≫ Kernel.Scheme.kernelInclusion f) = y ≫ fst A X) :
    FiberwiseMultiplication.ProductRel (fst A X) (snd A X) (crossPoint f g k l)
      (FiberwiseKernelCoordinates.kernelPoint g AxisData.replaceSecond l x) (FiberwiseKernelCoordinates.kernelPoint g AxisData.replaceSecond l y) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [crossPoint_fst, verticalPoint_fst, verticalPoint_fst, mul_comm]
    exact h
  · rw [crossPoint_snd, verticalPoint_snd]
  · rw [crossPoint_snd, verticalPoint_snd]

variable [GrpObj X] [IsCommMonObj X]

omit [GrpObj A] [IsCommMonObj A] in
/-- The vertical product of the crossing fiber and horizontal kernel fiber is the translated horizontal fiber. -/
theorem verticalCross_product {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (l : T ⟶ Kernel.Scheme.kernelObject g)
    (x z : T ⟶ A ⊗ X) (h : (x ≫ snd A X) * (l ≫ Kernel.Scheme.kernelInclusion g) = z ≫ snd A X) :
    FiberwiseMultiplication.ProductRel (snd A X) (fst A X) (crossPoint f g k l)
      (FiberwiseKernelCoordinates.kernelPoint f AxisData.replaceFirst k x) (FiberwiseKernelCoordinates.kernelPoint f AxisData.replaceFirst k z) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [crossPoint_snd, horizontalPoint_snd, horizontalPoint_snd, mul_comm]
    exact h
  · rw [crossPoint_fst, horizontalPoint_fst]
  · rw [crossPoint_fst, horizontalPoint_fst]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.KernelRectangle
