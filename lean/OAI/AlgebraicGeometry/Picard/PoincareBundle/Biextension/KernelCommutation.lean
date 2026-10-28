import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.KernelRectangle

/-! # Kernel Commutation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.KernelCommutation

noncomputable section

/-!
# Isotropic kernel frames make the constructed biextension kernel translations commute
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseKernelCoordinates
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.KernelRectangle

variable {S : Scheme.{u}} {A B X Y : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f] [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)

/-- Horizontal transport by a specified represented kernel point. -/
def kernelHorizontal {T : Over S} (x y : T ⟶ A ⊗ X) (k : T ⟶ Kernel.Scheme.kernelObject f)
    (h : (x ≫ fst A X) * (k ≫ Kernel.Scheme.kernelInclusion f) = y ≫ fst A X) (hb : x ≫ snd A X = y ≫ snd A X) :
    Line.Fibers.fiber L x ⟶ Line.Fibers.fiber L y :=
  FiberwiseKernelTransport.transport (fst A X) (snd A X) f AxisData.replaceFirst
    AxisData.replaceFirst_group AxisData.replaceFirst_base L Dh Kh x y k h hb

/-- Vertical transport by a specified represented kernel point. -/
def kernelVertical {T : Over S} (x z : T ⟶ A ⊗ X) (l : T ⟶ Kernel.Scheme.kernelObject g)
    (h : (x ≫ snd A X) * (l ≫ Kernel.Scheme.kernelInclusion g) = z ≫ snd A X) (hb : x ≫ fst A X = z ≫ fst A X) :
    Line.Fibers.fiber L x ⟶ Line.Fibers.fiber L z :=
  FiberwiseKernelTransport.transport (snd A X) (fst A X) g AxisData.replaceSecond
    AxisData.replaceSecond_group AxisData.replaceSecond_base L Dv Kv x z l h hb

variable (hi : Compatibility.Interchange L Dh Dv) (ht : Compatibility.TransverseFrames L Dh Dv f g Kh Kv)
  (he : Compatibility.Isotropic L Dh Dv f g Kh Kv)

include hi ht he in
/-- The four actual kernel translations commute because the kernel-intersection obstruction vanishes. -/
theorem translations_commute {T : Over S} (x y z w : T ⟶ A ⊗ X)
    (k : T ⟶ Kernel.Scheme.kernelObject f) (l : T ⟶ Kernel.Scheme.kernelObject g)
    (hxy : (x ≫ fst A X) * (k ≫ Kernel.Scheme.kernelInclusion f) = y ≫ fst A X)
    (hxz : (x ≫ snd A X) * (l ≫ Kernel.Scheme.kernelInclusion g) = z ≫ snd A X)
    (hyw : (y ≫ snd A X) * (l ≫ Kernel.Scheme.kernelInclusion g) = w ≫ snd A X)
    (hzw : (z ≫ fst A X) * (k ≫ Kernel.Scheme.kernelInclusion f) = w ≫ fst A X)
    (bxy : x ≫ snd A X = y ≫ snd A X) (bxz : x ≫ fst A X = z ≫ fst A X)
    (byw : y ≫ fst A X = w ≫ fst A X) (bzw : z ≫ snd A X = w ≫ snd A X) :
    kernelHorizontal f L Dh Kh x y k hxy bxy ≫ kernelVertical g L Dv Kv y w l hyw byw =
      kernelVertical g L Dv Kv x z l hxz bxz ≫ kernelHorizontal f L Dh Kh z w k hzw bzw :=
  Compatibility.contracted_square L Dh Dv f g Kh Kv hi ht he k l (KernelRectangle.crossPoint f g k l)
    (FiberwiseKernelCoordinates.kernelPoint f AxisData.replaceFirst k x) (FiberwiseKernelCoordinates.kernelPoint g AxisData.replaceSecond l x) x
    (FiberwiseKernelCoordinates.kernelPoint f AxisData.replaceFirst k z) (FiberwiseKernelCoordinates.kernelPoint g AxisData.replaceSecond l y) y z w
    (FiberwiseKernelCoordinates.translation_product (fst A X) (snd A X) f AxisData.replaceFirst AxisData.replaceFirst_group AxisData.replaceFirst_base x y k hxy bxy)
    (FiberwiseKernelCoordinates.translation_product (snd A X) (fst A X) g AxisData.replaceSecond AxisData.replaceSecond_group AxisData.replaceSecond_base x z l hxz bxz)
    (KernelRectangle.horizontalCross_product f g k l x y hxy) (KernelRectangle.verticalCross_product f g k l x z hxz)
    (FiberwiseKernelCoordinates.translation_product (snd A X) (fst A X) g AxisData.replaceSecond AxisData.replaceSecond_group AxisData.replaceSecond_base y w l hyw byw)
    (FiberwiseKernelCoordinates.translation_product (fst A X) (snd A X) f AxisData.replaceFirst AxisData.replaceFirst_group AxisData.replaceFirst_base z w k hzw bzw)
    (KernelRectangle.horizontalPoint_fst f k x).symm (KernelRectangle.horizontalPoint_fst f k z).symm
    (KernelRectangle.verticalPoint_snd g l x).symm (KernelRectangle.verticalPoint_snd g l y).symm
    (KernelRectangle.crossPoint_fst f g k l).symm (KernelRectangle.crossPoint_snd f g k l).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.KernelCommutation
