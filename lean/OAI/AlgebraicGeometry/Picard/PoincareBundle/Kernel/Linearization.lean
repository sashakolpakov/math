import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Pair
import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-! # Linearization -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Linearization

noncomputable section

/-!
# Kernel-equivariant transport gives ordinary descent data

The construction uses points over every test object and the represented
scheme-theoretic kernel. In particular, it retains nonreduced kernels.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open scoped _root_.CategoryTheory.MonObj

universe u v u' v'

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Pair

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]
  {A B : C} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

attribute [local instance] Scheme.kernelGroup

/-- The kernel-valued difference carries the first point to the second. -/
theorem difference_translates {T : C} (x y : T ⟶ A) (h : x ≫ f = y ≫ f) :
    x * (Pair.pointDifference f x y h ≫ Scheme.kernelInclusion f) = y := by
  rw [Pair.pointDifference_comp_inclusion, mul_inv_cancel_left]

/-- The full kernel-valued difference commutes with change of test object. -/
theorem difference_naturality {T T' : C} (g : T' ⟶ T) (x y : T ⟶ A)
    (h : x ≫ f = y ≫ f) (x' y' : T' ⟶ A) (h' : x' ≫ f = y' ≫ f)
    (hx : g ≫ x = x') (hy : g ≫ y = y') :
    g ≫ Pair.pointDifference f x y h = Pair.pointDifference f x' y' h' := by
  apply (cancel_mono (Scheme.kernelInclusion f)).mp
  rw [Category.assoc, Pair.pointDifference_comp_inclusion, MonObj.comp_mul,
    GrpObj.comp_inv, hx, hy, Pair.pointDifference_comp_inclusion]

variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  (L : F.obj (.mk (op A)))

/-- The object pulled back to an arbitrary test point of the group object. -/
abbrev pointObject {T : C} (x : T ⟶ A) : F.obj (.mk (op T)) :=
  (F.map x.op.toLoc).toFunctor.obj L

/-- A kernel action on the pulled-back object, natural on all test objects.
The identities are the ordinary unit, action-composition, and base-change laws. -/
structure KernelLinearization where
  transport ⦃T : C⦄ (x y : T ⟶ A) (k : T ⟶ Scheme.kernelObject f)
    (_hk : x * (k ≫ Scheme.kernelInclusion f) = y) : pointObject F L x ⟶ pointObject F L y
  unit_compat ⦃T : C⦄ (x : T ⟶ A)
    (hx : x * ((1 : T ⟶ Scheme.kernelObject f) ≫ Scheme.kernelInclusion f) = x) :
    transport x x 1 hx = 𝟙 _
  mul_compat ⦃T : C⦄ (x y z : T ⟶ A) (k l m : T ⟶ Scheme.kernelObject f)
    (hx : x * (k ≫ Scheme.kernelInclusion f) = y)
    (hy : y * (l ≫ Scheme.kernelInclusion f) = z)
    (hz : x * (m ≫ Scheme.kernelInclusion f) = z) (hm : k * l = m) :
    transport x y k hx ≫ transport y z l hy = transport x z m hz
  pullback_compat ⦃T T' : C⦄ (g : T' ⟶ T)
    (x y : T ⟶ A) (k : T ⟶ Scheme.kernelObject f) (hk : x * (k ≫ Scheme.kernelInclusion f) = y)
    (x' y' : T' ⟶ A) (k' : T' ⟶ Scheme.kernelObject f)
    (hk' : x' * (k' ≫ Scheme.kernelInclusion f) = y')
    (hx : g ≫ x = x') (hy : g ≫ y = y') (hkk : g ≫ k = k') :
    pullHom (transport x y k hk) g x' y' hx hy = transport x' y' k' hk'

/-- Equivariant transport along the actual kernel produces ordinary Čech descent data. -/
def KernelLinearization.toDescentData (D : KernelLinearization f F L) :
    F.DescentData (fun (_ : PUnit.{1}) => f) where
  obj _ := L
  hom T q _i₁ _i₂ x y hx hy :=
    D.transport x y (Pair.pointDifference f x y (hx.trans hy.symm))
      (difference_translates f x y (hx.trans hy.symm))
  pullHom_hom T' T g q q' hq _i₁ _i₂ x y hx hy x' y' hxx hyy := by
    apply D.pullback_compat
    exact difference_naturality f g x y _ x' y' _ hxx hyy
  hom_self T q _i x hx := by
    change D.transport x x (Pair.pointDifference f x x (hx.trans hx.symm)) _ = 𝟙 _
    simpa only [Pair.pointDifference_self] using
      D.unit_compat x (by rw [MonObj.one_comp, mul_one])
  hom_comp T q _i₁ _i₂ _i₃ x y z hx hy hz := by
    apply D.mul_compat
    exact (Pair.pointDifference_cocycle f x y z (hx.trans hy.symm) (hy.trans hz.symm)).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Linearization
