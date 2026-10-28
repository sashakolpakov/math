import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.KernelCommutation

/-! # Quotient Commutation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.QuotientCommutation

noncomputable section

/-!
# Isotropy gives commuting ordinary quotient transports in the two coordinates
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Pair OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.RectangularCoordinates
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.KernelCommutation
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

/-- The represented kernel difference depends only on the two actual points. -/
theorem pointDifference_congr {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
    (f : A ⟶ B) [IsMonHom f] {T : Over S} (a b a' b' : T ⟶ A)
    (h : a ≫ f = b ≫ f) (h' : a' ≫ f = b' ≫ f) (ha : a = a') (hb : b = b') :
    Kernel.Pair.pointDifference f a b h = Kernel.Pair.pointDifference f a' b' h' := by
  cases ha
  cases hb
  rfl

variable {S : Scheme.{u}} {A B X Y : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f] [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)

omit [GrpObj X] [IsCommMonObj X] in
/-- Horizontal quotient transport is the constructed transport by any equal kernel difference. -/
theorem horizontal_eq_kernel {T : Over S} (x y : T ⟶ A ⊗ X) (h : RectangularCoordinates.Horizontal f x y)
    (k : T ⟶ Kernel.Scheme.kernelObject f)
    (hk : Kernel.Pair.pointDifference f (x ≫ fst A X) (y ≫ fst A X) (AxisData.horizontalRelation f x y h).1 = k)
    (ht : (x ≫ fst A X) * (k ≫ Kernel.Scheme.kernelInclusion f) = y ≫ fst A X) :
    AxisData.horizontal f L Dh Kh x y h = KernelCommutation.kernelHorizontal f L Dh Kh x y k ht h.2 :=
  FiberwiseQuotientTransport.transport_using (fst A X) (snd A X) f AxisData.replaceFirst
    AxisData.replaceFirst_group AxisData.replaceFirst_base L Dh Kh x y (AxisData.horizontalRelation f x y h) k hk ht

omit [GrpObj A] [IsCommMonObj A] in
/-- Vertical quotient transport is the constructed transport by any equal kernel difference. -/
theorem vertical_eq_kernel {T : Over S} (x z : T ⟶ A ⊗ X) (h : RectangularCoordinates.Vertical g x z)
    (l : T ⟶ Kernel.Scheme.kernelObject g)
    (hl : Kernel.Pair.pointDifference g (x ≫ snd A X) (z ≫ snd A X) (AxisData.verticalRelation g x z h).1 = l)
    (ht : (x ≫ snd A X) * (l ≫ Kernel.Scheme.kernelInclusion g) = z ≫ snd A X) :
    AxisData.vertical g L Dv Kv x z h = KernelCommutation.kernelVertical g L Dv Kv x z l ht h.1 :=
  FiberwiseQuotientTransport.transport_using (snd A X) (fst A X) g AxisData.replaceSecond
    AxisData.replaceSecond_group AxisData.replaceSecond_base L Dv Kv x z (AxisData.verticalRelation g x z h) l hl ht

variable (hi : Compatibility.Interchange L Dh Dv) (ht : Compatibility.TransverseFrames L Dh Dv f g Kh Kv)
  (he : Compatibility.Isotropic L Dh Dv f g Kh Kv)

include hi ht he in
/-- The actual isotropy condition proves commutation for the constructed ordinary coordinate transports. -/
theorem axisData_commutes : RectangularTransport.Commutes f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf
    (AxisData.toAxisData f g L Dh Dv Kh Kv) := by
  intro T x y z w hxy hxz hyw hzw
  let k := Kernel.Pair.pointDifference f (x ≫ fst A X) (y ≫ fst A X) (AxisData.horizontalRelation f x y hxy).1
  let l := Kernel.Pair.pointDifference g (x ≫ snd A X) (z ≫ snd A X) (AxisData.verticalRelation g x z hxz).1
  have hk : Kernel.Pair.pointDifference f (z ≫ fst A X) (w ≫ fst A X) (AxisData.horizontalRelation f z w hzw).1 = k :=
    pointDifference_congr f _ _ _ _ _ _ hxz.1.symm hyw.1.symm
  have hl : Kernel.Pair.pointDifference g (y ≫ snd A X) (w ≫ snd A X) (AxisData.verticalRelation g y w hyw).1 = l :=
    pointDifference_congr g _ _ _ _ _ _ hxy.2.symm hzw.2.symm
  have hkx : (x ≫ fst A X) * (k ≫ Kernel.Scheme.kernelInclusion f) = y ≫ fst A X :=
    Kernel.Linearization.difference_translates f _ _ (AxisData.horizontalRelation f x y hxy).1
  have hlx : (x ≫ snd A X) * (l ≫ Kernel.Scheme.kernelInclusion g) = z ≫ snd A X :=
    Kernel.Linearization.difference_translates g _ _ (AxisData.verticalRelation g x z hxz).1
  have hkz : (z ≫ fst A X) * (k ≫ Kernel.Scheme.kernelInclusion f) = w ≫ fst A X := by
    rw [← hxz.1, ← hyw.1]
    exact hkx
  have hly : (y ≫ snd A X) * (l ≫ Kernel.Scheme.kernelInclusion g) = w ≫ snd A X := by
    rw [← hxy.2, ← hzw.2]
    exact hlx
  change AxisData.horizontal f L Dh Kh x y hxy ≫ AxisData.vertical g L Dv Kv y w hyw =
    AxisData.vertical g L Dv Kv x z hxz ≫ AxisData.horizontal f L Dh Kh z w hzw
  rw [horizontal_eq_kernel f L Dh Kh x y hxy k rfl hkx,
    vertical_eq_kernel g L Dv Kv y w hyw l hl hly,
    vertical_eq_kernel g L Dv Kv x z hxz l rfl hlx,
    horizontal_eq_kernel f L Dh Kh z w hzw k hk hkz]
  exact KernelCommutation.translations_commute f g L Dh Dv Kh Kv hi ht he x y z w k l hkx hlx hly hkz
    hxy.2 hxz.1 hyw.1 hzw.2

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.QuotientCommutation
