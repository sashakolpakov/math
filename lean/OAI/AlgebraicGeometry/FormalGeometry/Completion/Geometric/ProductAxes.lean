import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.Axes
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ProductAxis

/-! # Product Axes -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.ProductAxes.Construction

noncomputable section

/-! The actual geometric fiber of a product and its two identity-section axes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [reassoc] Frobenius.Construction.geometricFiberMap_fst Frobenius.Construction.geometricFiberMap_snd

universe u

variable (k : Type u) [Field k]

/-- The canonical product comparison on actual geometric fibers. -/
def geometricProductIso (A B : Over (Spec (CommRingCat.of k))) :
    Cohomology.Construction.geometricFiber (A ⊗ B) ≅
      pullback (Frobenius.Construction.geometricFiberOver k A).hom (Frobenius.Construction.geometricFiberOver k B).hom :=
  (Over.forget _).mapIso (prodComparisonIso (Over.pullback (Frobenius.Construction.algebraicClosureBase k)) A B)

@[reassoc (attr := simp)]
theorem geometricProductIso_inv_fst_fst (A B : Over (Spec (CommRingCat.of k))) :
    (geometricProductIso k A B).inv ≫
      pullback.fst (A ⊗ B).hom (Frobenius.Construction.algebraicClosureBase k) ≫ pullback.fst A.hom B.hom =
    pullback.fst (Frobenius.Construction.geometricFiberOver k A).hom (Frobenius.Construction.geometricFiberOver k B).hom ≫
      pullback.fst A.hom (Frobenius.Construction.algebraicClosureBase k) :=
  Over.prodComparisonIso_pullback_inv_left_fst_fst _ A B

@[reassoc (attr := simp)]
theorem geometricProductIso_inv_fst_snd (A B : Over (Spec (CommRingCat.of k))) :
    (geometricProductIso k A B).inv ≫
      pullback.fst (A ⊗ B).hom (Frobenius.Construction.algebraicClosureBase k) ≫ pullback.snd A.hom B.hom =
    pullback.snd (Frobenius.Construction.geometricFiberOver k A).hom (Frobenius.Construction.geometricFiberOver k B).hom ≫
      pullback.fst B.hom (Frobenius.Construction.algebraicClosureBase k) :=
  Over.prodComparisonIso_pullback_inv_left_fst_snd' _ A.hom B.hom

@[reassoc (attr := simp)]
theorem geometricProductIso_inv_snd (A B : Over (Spec (CommRingCat.of k))) :
    (geometricProductIso k A B).inv ≫ pullback.snd (A ⊗ B).hom (Frobenius.Construction.algebraicClosureBase k) =
    pullback.snd (Frobenius.Construction.geometricFiberOver k A).hom (Frobenius.Construction.geometricFiberOver k B).hom ≫
      (Frobenius.Construction.geometricFiberOver k B).hom :=
  Over.prodComparisonIso_pullback_inv_left_snd' _ A.hom B.hom

variable (A : Over (Spec (CommRingCat.of k))) [GrpObj A]

/-- The identity section after the actual algebraic-closure base change. -/
def geometricIdentitySection : Spec (CommRingCat.of (AlgebraicClosure k)) ⟶ Cohomology.Construction.geometricFiber A :=
  pullback.lift (Frobenius.Construction.algebraicClosureBase k ≫ (η[A]).left) (𝟙 _)
    (by simp [Category.assoc, (η[A]).w])

@[reassoc (attr := simp)]
theorem geometricIdentitySection_fst :
    geometricIdentitySection k A ≫ pullback.fst A.hom (Frobenius.Construction.algebraicClosureBase k) =
      Frobenius.Construction.algebraicClosureBase k ≫ (η[A]).left := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem geometricIdentitySection_hom :
    geometricIdentitySection k A ≫ (Frobenius.Construction.geometricFiberOver k A).hom = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The first actual product axis corresponds to the base change of the group first axis. -/
theorem geometricFirstAxis_comparison :
    (Proper.ProductAxis.Construction.properProductFirstAxisOver (Frobenius.Construction.geometricFiberOver k A) (Frobenius.Construction.geometricFiberOver k A)
      (geometricIdentitySection k A) (geometricIdentitySection_hom k A)).left ≫
        (geometricProductIso k A A).inv = Frobenius.Construction.geometricFiberMap k (Product.Axes.Construction.groupFirstAxis k A) := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [geometricProductIso_inv_fst_fst k A A,
        Frobenius.Construction.geometricFiberMap_fst_assoc k (Product.Axes.Construction.groupFirstAxis k A)]
      simp [Product.Axes.Construction.groupFirstAxis, Proper.ProductAxis.Construction.properProductFirstAxisOver, geometricIdentitySection]
    · simp only [Category.assoc]
      rw [geometricProductIso_inv_fst_snd k A A,
        Frobenius.Construction.geometricFiberMap_fst_assoc k (Product.Axes.Construction.groupFirstAxis k A)]
      simp [Product.Axes.Construction.groupFirstAxis, Proper.ProductAxis.Construction.properProductFirstAxisOver, geometricIdentitySection, Category.assoc]
      simpa only [Category.assoc] using
        (pullback.condition_assoc (f := A.hom) (g := Frobenius.Construction.algebraicClosureBase k) (η[A]).left).symm
  · simp only [Category.assoc]
    rw [geometricProductIso_inv_snd k A A, Frobenius.Construction.geometricFiberMap_snd k (Product.Axes.Construction.groupFirstAxis k A)]
    simp [Proper.ProductAxis.Construction.properProductFirstAxisOver, geometricIdentitySection, Category.assoc]

/-- The second actual product axis corresponds to the base change of the group second axis. -/
theorem geometricSecondAxis_comparison :
    Proper.AffineBaseChange.Construction.properProductSection (Frobenius.Construction.geometricFiberOver k A).hom (Frobenius.Construction.geometricFiberOver k A).hom
      (geometricIdentitySection k A) (geometricIdentitySection_hom k A) ≫
        (geometricProductIso k A A).inv = Frobenius.Construction.geometricFiberMap k (Product.Axes.Construction.groupSecondAxis k A) := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [geometricProductIso_inv_fst_fst k A A,
        Frobenius.Construction.geometricFiberMap_fst_assoc k (Product.Axes.Construction.groupSecondAxis k A)]
      simp [Product.Axes.Construction.groupSecondAxis, Proper.AffineBaseChange.Construction.properProductSection, geometricIdentitySection, Category.assoc]
      simpa only [Category.assoc] using
        (pullback.condition_assoc (f := A.hom) (g := Frobenius.Construction.algebraicClosureBase k) (η[A]).left).symm
    · simp only [Category.assoc]
      rw [geometricProductIso_inv_fst_snd k A A,
        Frobenius.Construction.geometricFiberMap_fst_assoc k (Product.Axes.Construction.groupSecondAxis k A)]
      simp [Product.Axes.Construction.groupSecondAxis, Proper.AffineBaseChange.Construction.properProductSection, geometricIdentitySection]
  · simp only [Category.assoc]
    rw [geometricProductIso_inv_snd k A A, Frobenius.Construction.geometricFiberMap_snd k (Product.Axes.Construction.groupSecondAxis k A)]
    simp [Proper.AffineBaseChange.Construction.properProductSection, geometricIdentitySection]

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.ProductAxes.Construction
