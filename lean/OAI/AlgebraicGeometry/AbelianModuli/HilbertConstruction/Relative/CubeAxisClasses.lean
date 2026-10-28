import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.CubeProducts
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductFamilyCover

/-! # Cube Axis Classes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.CubeAxisClasses

noncomputable section

/-! The two product axes of the original normalized cube class are
trivial over every base scheme. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
namespace Theta.Geometric

variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)
variable (L : Line.Bundles.LineBundle A.scheme.left)

theorem relativeCubeClass_left_axis :
    RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback
      (Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.left (A.scheme ⊗ A.scheme).hom A.scheme.hom
        η[A.scheme].left η[A.scheme].w)
      (Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))
        (CubeProducts.Theta.Geometric.relativeCubeFirst A) (CubeProducts.Theta.Geometric.relativeCubeSecond A) (CubeProducts.Theta.Geometric.relativeCubeThird A)) = 1 := by
  let j : A.scheme ⊗ A.scheme ⟶ CubeProducts.Theta.Geometric.relativeCubeProduct A :=
    lift (𝟙 (A.scheme ⊗ A.scheme)) (1 : A.scheme ⊗ A.scheme ⟶ A.scheme)
  have hj : Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.left (A.scheme ⊗ A.scheme).hom A.scheme.hom
      η[A.scheme].left η[A.scheme].w = j.left := by
    simp only [j, Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.left, Over.lift_left, Hom.one_def,
      Over.comp_left, Over.id_left, Over.toUnit_left]
  rw [hj]
  change RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback j.left
    (Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))
      (CubeProducts.Theta.Geometric.relativeCubeFirst A) (CubeProducts.Theta.Geometric.relativeCubeSecond A) (CubeProducts.Theta.Geometric.relativeCubeThird A)) = 1
  rw [Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass_pullback]
  have h₁ : j ≫ CubeProducts.Theta.Geometric.relativeCubeFirst A = fst A.scheme A.scheme := by
    dsimp only [j, CubeProducts.Theta.Geometric.relativeCubeFirst]
    rw [← Category.assoc, lift_fst, Category.id_comp]
  have h₂ : j ≫ CubeProducts.Theta.Geometric.relativeCubeSecond A = snd A.scheme A.scheme := by
    dsimp only [j, CubeProducts.Theta.Geometric.relativeCubeSecond]
    rw [← Category.assoc, lift_fst, Category.id_comp]
  have h₃ : j ≫ CubeProducts.Theta.Geometric.relativeCubeThird A = 1 :=
    lift_snd (𝟙 (A.scheme ⊗ A.scheme)) (1 : A.scheme ⊗ A.scheme ⟶ A.scheme)
  rw [h₁, h₂, h₃]
  simp only [Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass, mul_one, Picard.ThetaConstruction.RelativeCubeClasses.Geometric.identityNormalizedLine_one_class, div_self']

theorem relativeCubeClass_right_axis :
    RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback
      (Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.right (A.scheme ⊗ A.scheme).hom A.scheme.hom
        η[A.scheme ⊗ A.scheme].left η[A.scheme ⊗ A.scheme].w)
      (Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))
        (CubeProducts.Theta.Geometric.relativeCubeFirst A) (CubeProducts.Theta.Geometric.relativeCubeSecond A) (CubeProducts.Theta.Geometric.relativeCubeThird A)) = 1 := by
  let j : A.scheme ⟶ CubeProducts.Theta.Geometric.relativeCubeProduct A :=
    lift (1 : A.scheme ⟶ A.scheme ⊗ A.scheme) (𝟙 A.scheme)
  have hj : Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.right (A.scheme ⊗ A.scheme).hom A.scheme.hom
      η[A.scheme ⊗ A.scheme].left η[A.scheme ⊗ A.scheme].w = j.left := by
    simp only [j, Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.right, Over.lift_left, Hom.one_def,
      Over.comp_left, Over.id_left, Over.toUnit_left]
  rw [hj]
  change RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback j.left
    (Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))
      (CubeProducts.Theta.Geometric.relativeCubeFirst A) (CubeProducts.Theta.Geometric.relativeCubeSecond A) (CubeProducts.Theta.Geometric.relativeCubeThird A)) = 1
  rw [Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass_pullback]
  have h₁ : j ≫ CubeProducts.Theta.Geometric.relativeCubeFirst A = 1 := by
    dsimp only [j, CubeProducts.Theta.Geometric.relativeCubeFirst]
    rw [← Category.assoc, lift_fst, MonObj.one_comp]
  have h₂ : j ≫ CubeProducts.Theta.Geometric.relativeCubeSecond A = 1 := by
    dsimp only [j, CubeProducts.Theta.Geometric.relativeCubeSecond]
    rw [← Category.assoc, lift_fst, MonObj.one_comp]
  have h₃ : j ≫ CubeProducts.Theta.Geometric.relativeCubeThird A = 𝟙 A.scheme :=
    lift_snd (1 : A.scheme ⟶ A.scheme ⊗ A.scheme) (𝟙 A.scheme)
  rw [h₁, h₂, h₃]
  simp only [Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass, one_mul, Picard.ThetaConstruction.RelativeCubeClasses.Geometric.identityNormalizedLine_one_class, mul_one, div_self']

end Theta.Geometric

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.CubeAxisClasses
