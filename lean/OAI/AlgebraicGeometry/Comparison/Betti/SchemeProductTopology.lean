import OAI.AlgebraicGeometry.Comparison.Betti.TensorPointTopology
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeAffineCover
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointClosedMap

/-! # Scheme Product Topology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SchemeProductTopology

noncomputable section

/-!
# Analytic topology of actual scheme products

The inverse of the pair of scheme projections is continuous on each pair
of affine charts by the tensor-product evaluation calculation. The charts
are actual open embeddings, so this proves continuity on the whole product.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase)

def productScheme : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (pullback.snd X.hom Y.hom ≫ Y.hom)

def productLeft : productScheme X Y ⟶ X :=
  Over.homMk (pullback.fst X.hom Y.hom) pullback.condition

def productRight : productScheme X Y ⟶ Y :=
  Over.homMk (pullback.snd X.hom Y.hom) rfl

def productLift {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : T ⟶ X) (g : T ⟶ Y) :
    T ⟶ productScheme X Y :=
  Over.homMk (pullback.lift f.left g.left ((Over.w f).trans (Over.w g).symm)) (by
    change (pullback.lift _ _ _) ≫ (pullback.snd X.hom Y.hom ≫ Y.hom) = T.hom
    rw [← Category.assoc, pullback.lift_snd, Over.w g])

@[simp]
theorem productLift_left {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : T ⟶ X) (g : T ⟶ Y) :
    productLift X Y f g ≫ productLeft X Y = f := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

@[simp]
theorem productLift_right {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : T ⟶ X) (g : T ⟶ Y) :
    productLift X Y f g ≫ productRight X Y = g := by
  apply Over.OverMorphism.ext
  exact pullback.lift_snd _ _ _

theorem product_hom_ext {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} {f g : T ⟶ productScheme X Y}
    (h₁ : f ≫ productLeft X Y = g ≫ productLeft X Y)
    (h₂ : f ≫ productRight X Y = g ≫ productRight X Y) : f = g := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact congrArg (fun a => a.left) h₁
  · exact congrArg (fun a => a.left) h₂

def productPoint (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (productScheme X Y) := productLift X Y p.1 p.2

variable {X Y}

def tensorToProduct (A B : CommAlgCat ℂ) (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X)
    (g : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ Y) : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (A ⊗[ℂ] B) ⟶ productScheme X Y :=
  productLift X Y
    (Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (A ⊗[ℂ] B) Algebra.TensorProduct.includeLeft ≫ f)
    (Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ B (A ⊗[ℂ] B) Algebra.TensorProduct.includeRight ≫ g)

theorem productPoint_affineTest (A B : CommAlgCat ℂ) (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X)
    (g : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ Y) (p : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A × Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    productPoint X Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A f p.1, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B g p.2) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ (A ⊗[ℂ] B)) (tensorToProduct A B f g)
        (TensorPointTopology.tensorPoint A B p) := by
  apply product_hom_ext X Y
  · change productLift X Y _ _ ≫ productLeft X Y =
      (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv _ _ ≫ productLift X Y _ _) ≫ productLeft X Y
    rw [productLift_left, Category.assoc, productLift_left, ← Category.assoc,
      ← ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv_comap]
    change ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A p.1 ≫ f =
      ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A ((TensorPointTopology.tensorPoint A B p).comp Algebra.TensorProduct.includeLeft) ≫ f
    congr 1
    exact congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A)
      (Algebra.TensorProduct.lift_comp_includeLeft p.1 p.2 (fun _ _ => Commute.all _ _)).symm
  · change productLift X Y _ _ ≫ productRight X Y =
      (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv _ _ ≫ productLift X Y _ _) ≫ productRight X Y
    rw [productLift_right, Category.assoc, productLift_right, ← Category.assoc,
      ← ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv_comap]
    change ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv B p.2 ≫ g =
      ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv B ((TensorPointTopology.tensorPoint A B p).comp Algebra.TensorProduct.includeRight) ≫ g
    congr 1
    exact congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv B)
      (Algebra.TensorProduct.lift_comp_includeRight' p.1 p.2 (fun _ _ => Commute.all _ _)).symm

theorem productPoint_affineTest_continuous (A B : CommAlgCat ℂ)
    (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (g : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ Y) :
    Continuous (fun p : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A × Foundations.Scheme.AffineComplexPoints.affineComplexPoints B =>
      productPoint X Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A f p.1, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B g p.2)) :=
  ((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_affinePointMap (CommAlgCat.of ℂ (A ⊗[ℂ] B)) (tensorToProduct A B f g)).comp
    (TensorPointTopology.tensorPoint_continuous A B)).congr (fun p => (productPoint_affineTest A B f g p).symm)

variable (X Y)

theorem productPoint_continuous : Continuous (productPoint X Y) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨x, y⟩
  obtain ⟨U, hU, a, ha⟩ := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineOpenPoint_lift X x
  obtain ⟨V, hV, b, hb⟩ := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineOpenPoint_lift Y y
  let e := Prod.map (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap Y V hV)
  have he : Topology.IsOpenEmbedding e :=
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_affineOpenPointMap X U hU).prodMap
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_affineOpenPointMap Y V hV)
  have hc : Continuous (productPoint X Y ∘ e) :=
    productPoint_affineTest_continuous (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y V)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y V hV)
  have h := he.continuousAt_iff.mp (hc.continuousAt (x := (a, b)))
  simpa only [e, Prod.map_apply, ha, hb] using h

def productPointsHomeomorph : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (productScheme X Y) ≃ₜ
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y where
  toFun p := (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (productLeft X Y) p, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (productRight X Y) p)
  invFun := productPoint X Y
  left_inv _p := product_hom_ext X Y (productLift_left X Y _ _) (productLift_right X Y _ _)
  right_inv _p := Prod.ext (productLift_left X Y _ _) (productLift_right X Y _ _)
  continuous_toFun := (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map (productLeft X Y)).prodMk (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map (productRight X Y))
  continuous_invFun := productPoint_continuous X Y

end

end OAI.AlgebraicGeometry.Comparison.Betti.SchemeProductTopology
