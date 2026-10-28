import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.KernelZeroSection

/-! # Difference -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The difference of two points with equal isogeny image is an actual point of its scheme-theoretic kernel. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {S : Scheme.{u}} {g h : ℕ} {A : Abelian.Schemes.AbelianScheme g S} {B : Abelian.Schemes.AbelianScheme h S}
variable (p : Abelian.Schemes.AbelianScheme.Isogeny A B)

def Abelian.Schemes.AbelianScheme.Isogeny.kernelDifference : Limits.pullback p.hom p.hom ⟶ p.kernelScheme :=
  (p.kernelSchemePointsEquiv _).symm
    ⟨pullback.snd p.hom p.hom / pullback.fst _ _, by
      change (pullback.snd p.hom p.hom / pullback.fst p.hom p.hom) ≫ p.hom = 1
      rw [GrpObj.div_comp, div_eq_one]
      exact pullback.condition.symm⟩

@[reassoc (attr := simp)] theorem Abelian.Schemes.AbelianScheme.Isogeny.kernelDifference_inclusion :
    p.kernelDifference ≫ p.kernelInclusion = pullback.snd p.hom p.hom / pullback.fst _ _ :=
  congrArg (fun x : p.kernelAt (Limits.pullback p.hom p.hom) => x.val)
    ((p.kernelSchemePointsEquiv _).apply_symm_apply _)

theorem Abelian.Schemes.AbelianScheme.Isogeny.kernelDifference_diagonal :
    pullback.diagonal p.hom ≫ p.kernelDifference = toUnit A.scheme ≫ p.kernelZeroSection := by
  have : IsClosedImmersion p.kernelInclusion.left := p.kernelInclusion_closedImmersion
  have : Mono ((Over.forget S).map p.kernelInclusion) := inferInstanceAs (Mono p.kernelInclusion.left)
  have : Mono p.kernelInclusion := Functor.mono_of_mono_map (Over.forget S) inferInstance
  apply (cancel_mono p.kernelInclusion).mp
  simp only [Category.assoc, Abelian.Schemes.AbelianScheme.Isogeny.kernelDifference_inclusion, Abelian.Schemes.AbelianScheme.Isogeny.kernelZeroSection_inclusion,
    GrpObj.comp_div, pullback.diagonal_fst, pullback.diagonal_snd, MonObj.comp_one, div_self']

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
