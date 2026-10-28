import OAI.AlgebraicGeometry.FormalGeometry.Completion.AdicScalarRestriction
import Mathlib.RingTheory.AdicCompletion.Exactness

/-! # Adic Algebra Exactness -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.AdicAlgebraExactness.Construction

noncomputable section

/-! Artin--Rees exactness for completion at a base ideal on finite modules over a Noetherian algebra. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)
  {M N P : Type u} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]

theorem adicScalarRestrictionEquiv_naturality (f : M →ₗ[S] N) (x : AdicCompletion I M) :
    AdicScalarRestriction.Construction.adicScalarRestrictionEquiv (S := S) I N (AdicCompletion.map I (f.restrictScalars R) x) =
      AdicCompletion.map (I.map (algebraMap R S)) f (AdicScalarRestriction.Construction.adicScalarRestrictionEquiv (S := S) I M x) := by
  apply AdicCompletion.ext
  intro n
  change AdicScalarRestriction.Construction.adicScalarRestrictionQuotientEquiv (S := S) I N n
    ((f.restrictScalars R).reduceModIdeal (I ^ n) (x.val n)) =
      f.reduceModIdeal ((I.map (algebraMap R S)) ^ n)
        (AdicScalarRestriction.Construction.adicScalarRestrictionQuotientEquiv (S := S) I M n (x.val n))
  induction x.val n using Submodule.Quotient.induction_on with | _ m => rfl

/-- Base-ideal completion preserves injections of finite modules over the chart algebra. -/
theorem adicCompletion_map_injective_of_finite_over_algebra [IsNoetherianRing S]
    [Module.Finite S N] (f : M →ₗ[S] N) (hf : Function.Injective f) :
    Function.Injective (AdicCompletion.map I (f.restrictScalars R)) := by
  intro x y hxy
  apply (AdicScalarRestriction.Construction.adicScalarRestrictionEquiv (S := S) I M).injective
  apply AdicCompletion.map_injective (I.map (algebraMap R S)) hf
  rw [← adicScalarRestrictionEquiv_naturality, ← adicScalarRestrictionEquiv_naturality, hxy]

/-- Base-ideal completion is exact on a short exact sequence of finite chart modules. -/
theorem adicCompletion_map_exact_of_finite_over_algebra [IsNoetherianRing S]
    [Module.Finite S N] (f : M →ₗ[S] N) (g : N →ₗ[S] P)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (AdicCompletion.map I (f.restrictScalars R))
      (AdicCompletion.map I (g.restrictScalars R)) := by
  intro y
  constructor
  · intro hy
    have hy' : AdicCompletion.map (I.map (algebraMap R S)) g
        (AdicScalarRestriction.Construction.adicScalarRestrictionEquiv (S := S) I N y) = 0 := by
      rw [← adicScalarRestrictionEquiv_naturality, hy, map_zero]
    obtain ⟨x, hx⟩ := (AdicCompletion.map_exact hf hfg hg
      (AdicScalarRestriction.Construction.adicScalarRestrictionEquiv (S := S) I N y)).mp hy'
    refine ⟨(AdicScalarRestriction.Construction.adicScalarRestrictionEquiv (S := S) I M).symm x, ?_⟩
    apply (AdicScalarRestriction.Construction.adicScalarRestrictionEquiv (S := S) I N).injective
    rw [adicScalarRestrictionEquiv_naturality, LinearEquiv.apply_symm_apply, hx]
  · rintro ⟨x, rfl⟩
    apply (AdicScalarRestriction.Construction.adicScalarRestrictionEquiv (S := S) I P).injective
    rw [map_zero, adicScalarRestrictionEquiv_naturality, adicScalarRestrictionEquiv_naturality]
    exact (AdicCompletion.map_exact hf hfg hg _).mpr ⟨_, rfl⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.AdicAlgebraExactness.Construction
