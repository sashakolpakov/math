import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Adic Completion Linear -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionLinear

noncomputable section

/-! # Adic completion as an additive functor on modules over the original ring -/

open _root_.CategoryTheory

universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  {M N P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]

def map (f : M →ₗ[R] N) : AdicCompletion I M →ₗ[R] AdicCompletion I N :=
  (AdicCompletion.map I f).restrictScalars R

theorem map_zero : AdicCompletionLinear.map I (0 : M →ₗ[R] N) = 0 := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (AdicCompletion.map_zero I) x

theorem map_add (f g : M →ₗ[R] N) : AdicCompletionLinear.map I (f + g) = AdicCompletionLinear.map I f + AdicCompletionLinear.map I g := by
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  change (f + g).reduceModIdeal (I ^ n) (x.val n) =
    f.reduceModIdeal (I ^ n) (x.val n) + g.reduceModIdeal (I ^ n) (x.val n)
  generalize x.val n = q
  induction q using Submodule.Quotient.induction_on with
  | H z => rfl

theorem map_smul (a : R) (f : M →ₗ[R] N) : AdicCompletionLinear.map I (a • f) = a • AdicCompletionLinear.map I f := by
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  change (a • f).reduceModIdeal (I ^ n) (x.val n) = a • f.reduceModIdeal (I ^ n) (x.val n)
  generalize x.val n = q
  induction q using Submodule.Quotient.induction_on with
  | H z => rfl

theorem map_id : AdicCompletionLinear.map I (LinearMap.id : Module.End R M) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (AdicCompletion.map_id I M) x

theorem map_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) : (AdicCompletionLinear.map I g).comp (AdicCompletionLinear.map I f) = AdicCompletionLinear.map I (g.comp f) := by
  apply LinearMap.ext
  intro x
  exact AdicCompletion.map_comp_apply I f g x

def functor : ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (AdicCompletion I M)
  map f := ModuleCat.ofHom (AdicCompletionLinear.map I f.hom)
  map_id M := ModuleCat.hom_ext (AdicCompletionLinear.map_id I (M := M))
  map_comp f g := ModuleCat.hom_ext (AdicCompletionLinear.map_comp I f.hom g.hom).symm

instance : (functor I).Additive where
  map_add {_M _N} f g := ModuleCat.hom_ext (AdicCompletionLinear.map_add I f.hom g.hom)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionLinear
