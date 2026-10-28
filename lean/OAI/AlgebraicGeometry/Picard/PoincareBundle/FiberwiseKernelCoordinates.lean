import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Linearization

/-! # Fiberwise Kernel Coordinates -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseKernelCoordinates

noncomputable section

/-!
# Kernel translations in one actual coordinate of a product scheme
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {S : Scheme.{u}} {E A B X : Over S} [GrpObj A] [GrpObj B]
  (p : E ⟶ A) (r : E ⟶ X) (f : A ⟶ B) [IsMonHom f]
  (replace : A ⊗ E ⟶ E) (hp : replace ≫ p = fst A E) (hr : replace ≫ r = snd A E ≫ r)

attribute [local instance] Kernel.Scheme.kernelGroup Kernel.Scheme.kernelGroup_commutative

/-- Replace the group coordinate by an included kernel point, retaining the other coordinate. -/
def kernelPoint {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (x : T ⟶ E) : T ⟶ E :=
  lift (k ≫ Kernel.Scheme.kernelInclusion f) x ≫ replace

include hp in
omit [GrpObj A] [IsMonHom f] in
/-- The new group coordinate is exactly the included scheme-theoretic kernel point. -/
theorem kernelPoint_group {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (x : T ⟶ E) :
    kernelPoint f replace k x ≫ p = k ≫ Kernel.Scheme.kernelInclusion f := by
  dsimp only [kernelPoint]
  rw [Category.assoc, hp, lift_fst]

include hr in
omit [GrpObj A] [IsMonHom f] in
/-- Replacement preserves the fixed coordinate. -/
theorem kernelPoint_base {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (x : T ⟶ E) :
    kernelPoint f replace k x ≫ r = x ≫ r := by
  dsimp only [kernelPoint]
  rw [Category.assoc, hr, lift_snd_assoc]

omit [GrpObj A] [IsMonHom f] in
/-- The replacement point is natural on every test scheme. -/
theorem kernelPoint_natural {T T' : Over S} (g : T' ⟶ T)
    (k : T ⟶ Kernel.Scheme.kernelObject f) (x : T ⟶ E) (k' : T' ⟶ Kernel.Scheme.kernelObject f) (x' : T' ⟶ E)
    (hk : g ≫ k = k') (hx : g ≫ x = x') :
    g ≫ kernelPoint f replace k x = kernelPoint f replace k' x' := by
  dsimp only [kernelPoint]
  rw [comp_lift_assoc, ← Category.assoc g k (Kernel.Scheme.kernelInclusion f), hk, hx]

variable [IsCommMonObj A]

include hp hr in
omit [IsMonHom f] in
/-- Kernel translation gives exactly the three-point relation for the actual line multiplication. -/
theorem translation_product {T : Over S} (x y : T ⟶ E) (k : T ⟶ Kernel.Scheme.kernelObject f)
    (hxy : (x ≫ p) * (k ≫ Kernel.Scheme.kernelInclusion f) = y ≫ p) (hb : x ≫ r = y ≫ r) :
    FiberwiseMultiplication.ProductRel p r (kernelPoint f replace k x) x y := by
  refine ⟨?_, kernelPoint_base r f replace hr k x, ?_⟩
  · rw [kernelPoint_group p f replace hp, mul_comm]
    exact hxy
  · exact (kernelPoint_base r f replace hr k x).trans hb

include hp hr in
/-- The two normalized kernel points multiply to the normalized product-kernel point. -/
theorem kernel_product {T : Over S} (x y : T ⟶ E) (k l m : T ⟶ Kernel.Scheme.kernelObject f)
    (hm : k * l = m) (hb : x ≫ r = y ≫ r) :
    FiberwiseMultiplication.ProductRel p r (kernelPoint f replace l y) (kernelPoint f replace k x)
      (kernelPoint f replace m x) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [kernelPoint_group p f replace hp, kernelPoint_group p f replace hp,
      kernelPoint_group p f replace hp, ← MonObj.mul_comp, mul_comm l k, hm]
  · rw [kernelPoint_base r f replace hr, kernelPoint_base r f replace hr]
    exact hb.symm
  · rw [kernelPoint_base r f replace hr, kernelPoint_base r f replace hr]
    exact hb.symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseKernelCoordinates
