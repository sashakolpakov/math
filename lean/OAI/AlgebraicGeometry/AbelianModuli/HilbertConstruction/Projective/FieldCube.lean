import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.CubeProducts
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.FieldFrameReflection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineTrivializationOf
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Field Cube -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.FieldCube

noncomputable section

/-! The cube identity over every field follows by reflecting the
actual geometric frame along its algebraic closure. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

namespace Theta.Geometric

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products

theorem projective_field_universal_cube
    {K : Type u} [Field K] {g : ℕ} (A : Abelian.Schemes.AbelianScheme g (Spec (.of K)))
    (P : ProjectivePresentations.ProjectivePresentation A.scheme) (q : Line.Bundles.LineBundle.IsoClass A.scheme.left) :
    Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass q (Relative.CubeProducts.Theta.Geometric.relativeCubeFirst A) (Relative.CubeProducts.Theta.Geometric.relativeCubeSecond A) (Relative.CubeProducts.Theta.Geometric.relativeCubeThird A) = 1 := by
  let c := Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  let v := Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass q (Relative.CubeProducts.Theta.Geometric.relativeCubeFirst A) (Relative.CubeProducts.Theta.Geometric.relativeCubeSecond A) (Relative.CubeProducts.Theta.Geometric.relativeCubeThird A)
  let L : Line.Bundles.LineBundle (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).left := v.out
  have hL : Line.Bundles.LineBundle.classOf L = v := Quotient.out_eq _
  let s := (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).left
  have hs : s ≫ (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).hom = 𝟙 _ :=
    (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).w
  obtain ⟨r⟩ := Quotients.FiniteDescent.LineTrivializationOf.Construction.LineTrivialization.pullback_trivial_over_field s L
  have he : Nonempty
      ((L.pullback (pullback.fst (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).hom c)).sheaf ≅
        Line.Bundles.structureModule (pullback (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).hom c)) := by
    apply @Quotient.exact _ (Line.Bundles.LineBundle.isoSetoid _)
      (L.pullback (pullback.fst (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).hom c)) (Line.Bundles.LineBundle.trivial _)
    change RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).hom c) (Line.Bundles.LineBundle.classOf L) = 1
    rw [hL]
    change RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).hom c)
      (Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass q (Relative.CubeProducts.Theta.Geometric.relativeCubeFirst A) (Relative.CubeProducts.Theta.Geometric.relativeCubeSecond A) (Relative.CubeProducts.Theta.Geometric.relativeCubeThird A)) = 1
    rw [Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass_baseChange]
    exact Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass_eq_one_overField (A.pullback c) _ _ _ _
  obtain ⟨e⟩ := Picard.ThetaConstruction.FieldFrameReflection.Geometric.field_line_trivial_of_cartesian_trivial
    (X := Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A) ((P.product P).product P) s hs L r
    (pullback.fst (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).hom c) (pullback.snd (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).hom c)
    c (IsPullback.of_hasPullback (Relative.CubeProducts.Theta.Geometric.relativeCubeProduct A).hom c) he.some
  exact hL.symm.trans (Quotient.sound ⟨e⟩)

theorem projective_field_cube
    {K : Type u} [Field K] {g : ℕ} (A : Abelian.Schemes.AbelianScheme g (Spec (.of K)))
    (P : ProjectivePresentations.ProjectivePresentation A.scheme) (q : Line.Bundles.LineBundle.IsoClass A.scheme.left)
    {U : Over (Spec (.of K))} (a b c : U ⟶ A.scheme) : Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass q a b c = 1 :=
  Relative.CubeProducts.Theta.Geometric.relativeCubeClass_eq_of_universal A q (projective_field_universal_cube A P q) a b c

end Theta.Geometric

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.FieldCube
