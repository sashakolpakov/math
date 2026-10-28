import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeCubeClasses
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.SchemeProducts

/-! # Cube Products -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.CubeProducts.Theta.Geometric

noncomputable section

/-! The actual triple product and its coordinate maps for the relative
cube identity. These definitions require no reducedness of the base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

def relativeCubeProduct : Over S := (A.scheme ⊗ A.scheme) ⊗ A.scheme

def relativeCubeFirst : relativeCubeProduct A ⟶ A.scheme :=
  fst (A.scheme ⊗ A.scheme) A.scheme ≫ fst A.scheme A.scheme

def relativeCubeSecond : relativeCubeProduct A ⟶ A.scheme :=
  fst (A.scheme ⊗ A.scheme) A.scheme ≫ snd A.scheme A.scheme

def relativeCubeThird : relativeCubeProduct A ⟶ A.scheme := snd (A.scheme ⊗ A.scheme) A.scheme

instance relativeCubeProduct_group : GrpObj (relativeCubeProduct A) :=
  inferInstanceAs (GrpObj ((A.scheme ⊗ A.scheme) ⊗ A.scheme))
instance relativeCubeFirst_group : IsMonHom (relativeCubeFirst A) :=
  inferInstanceAs (IsMonHom (fst (A.scheme ⊗ A.scheme) A.scheme ≫ fst A.scheme A.scheme))
instance relativeCubeSecond_group : IsMonHom (relativeCubeSecond A) :=
  inferInstanceAs (IsMonHom (fst (A.scheme ⊗ A.scheme) A.scheme ≫ snd A.scheme A.scheme))
instance relativeCubeThird_group : IsMonHom (relativeCubeThird A) :=
  inferInstanceAs (IsMonHom (snd (A.scheme ⊗ A.scheme) A.scheme))
instance relativeCubeProduct_proper : IsProper (relativeCubeProduct A).hom :=
  ((A.product A).product A).proper
instance relativeCubeProduct_smooth : Smooth (relativeCubeProduct A).hom :=
  inferInstanceAs (Smooth ((A.product A).product A).scheme.hom)
instance relativeCubeProduct_connected : GeometricallyConnected (relativeCubeProduct A).hom :=
  ((A.product A).product A).connected

theorem relativeCubeClass_eq_of_universal (q : Line.Bundles.LineBundle.IsoClass A.scheme.left)
    (hq : Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass q (relativeCubeFirst A) (relativeCubeSecond A) (relativeCubeThird A) = 1)
    {U : Over S} (a b c : U ⟶ A.scheme) : Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass q a b c = 1 := by
  let j : U ⟶ relativeCubeProduct A := lift (lift a b) c
  have h := congrArg (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback j.left) hq
  rw [map_one, Picard.ThetaConstruction.RelativeCubeClasses.Geometric.relativeCubeClass_pullback] at h
  have h₁ : j ≫ relativeCubeFirst A = a := by
    change lift (lift a b) c ≫ (fst (A.scheme ⊗ A.scheme) A.scheme ≫ fst A.scheme A.scheme) = a
    rw [← Category.assoc, lift_fst, lift_fst]
  have h₂ : j ≫ relativeCubeSecond A = b := by
    change lift (lift a b) c ≫ (fst (A.scheme ⊗ A.scheme) A.scheme ≫ snd A.scheme A.scheme) = b
    rw [← Category.assoc, lift_fst, lift_snd]
  have h₃ : j ≫ relativeCubeThird A = c := lift_snd (lift a b) c
  rw [h₁, h₂, h₃] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.CubeProducts.Theta.Geometric
