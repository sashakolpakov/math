import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.Difference
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.DiagonalComparison

/-! # Diagonal Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The isogeny diagonal is the inverse image of the kernel zero section. An unramified kernel therefore makes the isogeny formally unramified. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {S : Scheme.{u}} {g h : ℕ} {A : Abelian.Schemes.AbelianScheme g S} {B : Abelian.Schemes.AbelianScheme h S}
variable (p : Abelian.Schemes.AbelianScheme.Isogeny A B)

theorem Abelian.Schemes.AbelianScheme.Isogeny.kernelDifference_isPullback :
    IsPullback (toUnit A.scheme) (pullback.diagonal p.hom) p.kernelZeroSection p.kernelDifference := by
  apply IsPullback.mk' p.kernelDifference_diagonal.symm
  · intro T f k _ h
    exact (cancel_mono (pullback.diagonal p.hom)).mp h
  · intro T a b h
    have hc := congrArg (fun z : T ⟶ p.kernelScheme => z ≫ p.kernelInclusion) h
    have hd : b ≫ pullback.snd p.hom p.hom / (b ≫ pullback.fst p.hom p.hom) = 1 := by
      simpa only [Category.assoc, Abelian.Schemes.AbelianScheme.Isogeny.kernelZeroSection_inclusion, Abelian.Schemes.AbelianScheme.Isogeny.kernelDifference_inclusion,
        GrpObj.comp_div, MonObj.comp_one] using hc.symm
    have hb := div_eq_one.mp hd
    refine ⟨b ≫ pullback.fst _ _, toUnit_unique _ _, ?_⟩
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · simpa only [Category.assoc, pullback.diagonal_snd, Category.comp_id] using hb.symm

theorem Abelian.Schemes.AbelianScheme.Isogeny.formallyUnramified_of_kernel [FormallyUnramified p.kernelScheme.hom] :
    FormallyUnramified p.hom.left := by
  have H := p.kernelDifference_isPullback.map (Over.forget S)
  have hz : IsOpenImmersion p.kernelZeroSection.left := p.kernelZeroSection_isOpenImmersion
  have : IsOpenImmersion (pullback.diagonal p.hom).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) H hz
  exact HilbertConstruction.Over.DiagonalComparison.formallyUnramified_of_overDiagonal p.hom

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
