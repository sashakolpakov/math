import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.Difference

/-! # Kernel Torsor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The self-pullback of an isogeny is the source times its actual kernel: two points in one fiber differ by a unique kernel point. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {S : Scheme.{u}} {g h : ℕ} {A : Abelian.Schemes.AbelianScheme g S} {B : Abelian.Schemes.AbelianScheme h S}
variable (p : Abelian.Schemes.AbelianScheme.Isogeny A B)

def Abelian.Schemes.AbelianScheme.Isogeny.kernelActionPair : A.scheme ⊗ p.kernelScheme ⟶ Limits.pullback p.hom p.hom :=
  Limits.pullback.lift (fst A.scheme p.kernelScheme)
    (fst A.scheme p.kernelScheme * (snd A.scheme p.kernelScheme ≫ p.kernelInclusion)) (by
      simp only [MonObj.mul_comp, Category.assoc, Abelian.Schemes.AbelianScheme.Isogeny.kernelInclusion_comp, MonObj.comp_one, mul_one])

@[reassoc (attr := simp)]
theorem Abelian.Schemes.AbelianScheme.Isogeny.kernelActionPair_fst : p.kernelActionPair ≫ Limits.pullback.fst p.hom p.hom =
    fst A.scheme p.kernelScheme := Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem Abelian.Schemes.AbelianScheme.Isogeny.kernelActionPair_snd : p.kernelActionPair ≫ Limits.pullback.snd p.hom p.hom =
    fst A.scheme p.kernelScheme * (snd A.scheme p.kernelScheme ≫ p.kernelInclusion) :=
  Limits.pullback.lift_snd _ _ _

def Abelian.Schemes.AbelianScheme.Isogeny.kernelDifferencePair : Limits.pullback p.hom p.hom ⟶ A.scheme ⊗ p.kernelScheme :=
  lift (Limits.pullback.fst p.hom p.hom) p.kernelDifference

theorem Abelian.Schemes.AbelianScheme.Isogeny.kernelActionPair_difference : p.kernelActionPair ≫ p.kernelDifferencePair = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, Abelian.Schemes.AbelianScheme.Isogeny.kernelDifferencePair, lift_fst, Abelian.Schemes.AbelianScheme.Isogeny.kernelActionPair_fst, Category.id_comp]
  · have : Mono p.kernelInclusion := Functor.mono_of_mono_map (Over.forget S)
      (inferInstanceAs (Mono p.kernelInclusion.left))
    apply (cancel_mono p.kernelInclusion).mp
    simp only [Category.assoc, Abelian.Schemes.AbelianScheme.Isogeny.kernelDifferencePair, lift_snd, Abelian.Schemes.AbelianScheme.Isogeny.kernelDifference_inclusion,
      GrpObj.comp_div, Abelian.Schemes.AbelianScheme.Isogeny.kernelActionPair_snd, Abelian.Schemes.AbelianScheme.Isogeny.kernelActionPair_fst, Category.id_comp,
      mul_div_cancel_left]

theorem Abelian.Schemes.AbelianScheme.Isogeny.kernelDifferencePair_action : p.kernelDifferencePair ≫ p.kernelActionPair = 𝟙 _ := by
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, Abelian.Schemes.AbelianScheme.Isogeny.kernelActionPair_fst, Abelian.Schemes.AbelianScheme.Isogeny.kernelDifferencePair, lift_fst, Category.id_comp]
  · simp only [Category.assoc, Abelian.Schemes.AbelianScheme.Isogeny.kernelActionPair_snd, MonObj.comp_mul,
      Abelian.Schemes.AbelianScheme.Isogeny.kernelDifferencePair, lift_fst, lift_snd_assoc, Abelian.Schemes.AbelianScheme.Isogeny.kernelDifference_inclusion,
      Category.id_comp, mul_div_cancel]

def Abelian.Schemes.AbelianScheme.Isogeny.kernelTorsorIso : A.scheme ⊗ p.kernelScheme ≅ Limits.pullback p.hom p.hom where
  hom := p.kernelActionPair
  inv := p.kernelDifferencePair
  hom_inv_id := p.kernelActionPair_difference
  inv_hom_id := p.kernelDifferencePair_action

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
