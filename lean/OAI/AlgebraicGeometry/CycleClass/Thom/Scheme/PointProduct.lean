import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeAffineCover
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Point Product -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PointProduct.Constructions

noncomputable section

/-! The actual complex points of a scheme product carry the ordinary
product topology, proved using genuine affine tensor-product characters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.Topology MonoidalCategory TensorProduct

/-- The complex character of a tensor product determined by a pair of characters. -/
def affineTensorPair (A B : Type) [CommRing A] [Algebra ℂ A]
    [CommRing B] [Algebra ℂ B] (xy : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A × Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⊗[ℂ] B) :=
  Algebra.TensorProduct.lift xy.1 xy.2 (fun _ _ => Commute.all _ _)

/-- Pairing affine characters is continuous in their ordinary evaluation topologies. -/
theorem affineTensorPair_continuous (A B : Type) [CommRing A] [Algebra ℂ A]
    [CommRing B] [Algebra ℂ B] : Continuous (affineTensorPair A B) := by
  apply (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_iff _).mpr
  intro t
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add]; exact hx.add hy
  | tmul a b =>
    change Continuous (fun xy : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A × Foundations.Scheme.AffineComplexPoints.affineComplexPoints B => xy.1 a * xy.2 b)
    exact ((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval a).comp continuous_fst).mul
      ((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval b).comp continuous_snd)

/-- The actual scheme map from the tensor-product affine chart to a product. -/
def affineProductMap {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (A B : CommAlgCat ℂ)
    (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (g : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ Y) :
    Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (A ⊗[ℂ] B) ⟶ X ⊗ Y :=
  lift
    (Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (A ⊗[ℂ] B) Algebra.TensorProduct.includeLeft ≫ f)
    (Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ B (A ⊗[ℂ] B) Algebra.TensorProduct.includeRight ≫ g)

/-- The algebraic product chart has the expected value on complex points. -/
theorem affineProductMap_apply {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (A B : CommAlgCat ℂ)
    (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (g : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ Y)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ (A ⊗[ℂ] B))
        (affineProductMap A B f g) (affineTensorPair A B (x, y)) =
      lift (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A f x)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B g y) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap, affineProductMap, Category.assoc, lift_fst]
    rw [← Category.assoc, ← ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv_comap]
    change ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A
      ((Algebra.TensorProduct.lift x y _).comp Algebra.TensorProduct.includeLeft) ≫ f = _
    rw [Algebra.TensorProduct.lift_comp_includeLeft]
  · simp only [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap, affineProductMap, Category.assoc, lift_snd]
    rw [← Category.assoc, ← ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv_comap]
    change ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv B
      ((Algebra.TensorProduct.lift x y _).comp Algebra.TensorProduct.includeRight) ≫ g = _
    rw [Algebra.TensorProduct.lift_comp_includeRight']

/-- Pairing points is continuous on each pair of affine test spaces. -/
theorem affinePointPair_continuous {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (A B : CommAlgCat ℂ)
    (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (g : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ Y) :
    Continuous (fun xy : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A × Foundations.Scheme.AffineComplexPoints.affineComplexPoints B =>
      lift (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A f xy.1)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B g xy.2)) := by
  exact ((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_affinePointMap
    (CommAlgCat.of ℂ (A ⊗[ℂ] B)) (affineProductMap A B f g)).comp
      (affineTensorPair_continuous A B)).congr (fun xy => affineProductMap_apply A B f g xy.1 xy.2)

/-- Affine open charts prove continuity of the global point-pairing map. -/
theorem schemePointPair_continuous (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Continuous (fun xy : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y => lift xy.1 xy.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨x, y⟩
  obtain ⟨U, hU, u, rfl⟩ := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineOpenPoint_lift X x
  obtain ⟨V, hV, v, rfl⟩ := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineOpenPoint_lift Y y
  have ho := (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_affineOpenPointMap X U hU).prodMap
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_affineOpenPointMap Y V hV)
  have hc := (affinePointPair_continuous (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y V)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y V hV)).continuousAt (x := (u, v))
  exact (ho.continuousAt_iff
    (g := fun xy : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y => lift xy.1 xy.2)
    (x := (u, v))).mp hc

/-- Complex points of the scheme product carry the ordinary product topology. -/
def schemePointProductHomeomorph (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X ⊗ Y) ≃ₜ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) where
  toFun p := (p ≫ fst X Y, p ≫ snd X Y)
  invFun xy := lift xy.1 xy.2
  left_inv p := by simp
  right_inv xy := by simp
  continuous_toFun := (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map (fst X Y)).prodMk
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map (snd X Y))
  continuous_invFun := schemePointPair_continuous X Y

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PointProduct.Constructions
