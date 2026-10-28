import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.PowerClasses
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Homomorphism
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DualMaps
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Splitting

/-! # Scalar Classes -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.ScalarClasses

noncomputable section

/-! Actual Poincare products prove that represented duality preserves multiplication by an integer. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles OAI.AlgebraicGeometry.Picard.PoincareBundle.Functor OAI.AlgebraicGeometry.Picard.PoincareBundle.Homogeneous OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.Homogeneity
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Map OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.PowerClasses OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductParameters OAI.AlgebraicGeometry.Picard.PoincareBundle.DualMaps

variable {S : Scheme.{u}} {D A : Over S} [GrpObj D] [GrpObj A]
  (P : Line.Bundles.LineBundle (D ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst D A) (snd D A) P)
  (Dv : FiberwiseMultiplication.Multiplication (snd D A) (fst D A) P)

include Dh Dv

/-- Pullback by an integer in the family coordinate equals the same integer in the parameter coordinate. -/
theorem scalar_familyClass {T : Over S} (x : T ⟶ D) (n : ℕ) :
    Line.Bundles.LineBundleClass.pullback (Functor.familyMap ((𝟙 A) ^ n) T) (Vertical.Homogeneity.familyClass P x) = Vertical.Homogeneity.familyClass P (x ^ n) := by
  have hb := Biextension.PowerClasses.pow_balance P Dh Dv (fst T A ≫ x) (snd T A) n
  have hl : (𝟙 T ⊗ₘ (𝟙 A) ^ n) ≫ (x ⊗ₘ 𝟙 A) = lift (fst T A ≫ x) ((snd T A) ^ n) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [Category.assoc, MonObj.comp_pow]
  have hr : (x ^ n) ⊗ₘ 𝟙 A = lift ((fst T A ≫ x) ^ n) (snd T A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.comp_pow]
  change Line.Bundles.LineBundleClass.pullback (𝟙 T ⊗ₘ (𝟙 A) ^ n).left
    (Line.Bundles.LineBundleClass.pullback (x ⊗ₘ 𝟙 A).left (Line.Bundles.LineBundleClass.mk P)) =
      Line.Bundles.LineBundleClass.pullback ((x ^ n) ⊗ₘ 𝟙 A).left (Line.Bundles.LineBundleClass.mk P)
  have hl' : (𝟙 T ⊗ₘ (𝟙 A) ^ n).left ≫ (x ⊗ₘ 𝟙 A).left =
      (lift (fst T A ≫ x) ((snd T A) ^ n)).left := congrArg Over.Hom.left hl
  rw [← Line.Bundles.LineBundleClass.pullback_comp, hl', congrArg Over.Hom.left hr]
  exact hb.symm

variable [IsCommMonObj A]

/-- The scalar-coordinate equation holds already in the homogeneous presheaf. -/
theorem scalar_homogeneousClass {T : Over S} (x : T ⟶ D) (n : ℕ) :
    (Homogeneous.pullbackHomogeneousPresheaf ((𝟙 A) ^ n)).app (op T)
        (Product.Map.homogeneousClass P (Vertical.ProductParameters.globalProduct D A P Dv) (Vertical.ProductParameters.globalProduct_isIso D A P Dv) x) =
      Product.Map.homogeneousClass P (Vertical.ProductParameters.globalProduct D A P Dv) (Vertical.ProductParameters.globalProduct_isIso D A P Dv) (x ^ n) := by
  apply Subtype.ext
  exact scalar_familyClass P Dh Dv x n

/-- Sheafification preserves the proved scalar-coordinate equation. -/
theorem scalar_sectionClass {T : Over S} (x : T ⟶ D) (n : ℕ) :
    (Homogeneous.pullbackHomogeneousSheaf ((𝟙 A) ^ n)).hom.app (op T)
        (Product.Map.sectionClass P (Vertical.ProductParameters.globalProduct D A P Dv) (Vertical.ProductParameters.globalProduct_isIso D A P Dv) x) =
      Product.Map.sectionClass P (Vertical.ProductParameters.globalProduct D A P Dv) (Vertical.ProductParameters.globalProduct_isIso D A P Dv) (x ^ n) := by
  have h := congrArg (fun b => b.app (op T)
    (Product.Map.homogeneousClass P (Vertical.ProductParameters.globalProduct D A P Dv) (Vertical.ProductParameters.globalProduct_isIso D A P Dv) x))
    (toSheafify_naturality (Scheme.fppfTopology.over S) (Homogeneous.pullbackHomogeneousPresheaf ((𝟙 A) ^ n)))
  exact h.symm.trans (congrArg
    ((toSheafify (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf A)).app (op T))
    (scalar_homogeneousClass P Dh Dv x n))

/-- The dual of multiplication by an integer is multiplication by that integer on the represented dual. -/
theorem representedDualMap_scalar (HD : (Homogeneous.homogeneousSheaf A).obj.RepresentableBy D)
    (hP : HD.homEquiv (𝟙 D) =
      Product.Map.sectionClass P (Vertical.ProductParameters.globalProduct D A P Dv) (Vertical.ProductParameters.globalProduct_isIso D A P Dv) (𝟙 D)) (n : ℕ) :
    DualMaps.representedDualMap HD HD ((𝟙 A) ^ n) = (𝟙 D) ^ n := by
  apply HD.homEquiv.injective
  have h := DualMaps.representedDualMap_action HD HD ((𝟙 A) ^ n) (𝟙 D)
  rw [Category.id_comp, hP, scalar_sectionClass P Dh Dv] at h
  exact h.trans (Product.Homomorphism.universalSection_action P
    (Vertical.ProductParameters.globalProduct D A P Dv) (Vertical.ProductParameters.globalProduct_isIso D A P Dv) HD hP ((𝟙 D) ^ n)).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.ScalarClasses
