import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-! # Semilocal Ideal Principal -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SemilocalIdealPrincipal

noncomputable section

/-! Finite flat ideals in semilocal domains are principal. This allows
local defining equations at finitely many points to be combined into
one equation after the corresponding semilocalization. -/

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] [IsDomain R]

theorem ideal_rank_one (I : Ideal R) (hI : I ≠ ⊥) : Module.rank R I = 1 := by
  apply le_antisymm ((Submodule.rank_le I).trans_eq (Module.rank_self R))
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  apply Module.one_le_rank_iff.mpr
  refine ⟨LinearMap.toSpanSingleton R I ⟨a, ha⟩, ?_⟩
  apply LinearMap.ker_eq_bot.mp
  exact LinearMap.ker_toSpanSingleton R (fun h => ha0 (congrArg Subtype.val h))

theorem quotient_fiber_finrank (I : Ideal R) [Module.Finite R I] [Module.Flat R I]
    (hI : I ≠ ⊥) (p : MaximalSpectrum R) :
    letI := Ideal.Quotient.field p.asIdeal
    Module.finrank (R ⧸ p.asIdeal) ((R ⧸ p.asIdeal) ⊗[R] I) = 1 := by
  let := Ideal.Quotient.field p.asIdeal
  let K := p.asIdeal.ResidueField
  have he := (TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ p.asIdeal) K K I).finrank_eq
  rw [Module.finrank_baseChange] at he
  rw [he]
  change Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber I) = 1
  rw [Ideal.finrank_fiber_eq_finrank]
  exact Module.rank_eq_one_iff_finrank_eq_one.mp (ideal_rank_one R I hI)

theorem of_flat [Finite (MaximalSpectrum R)] (I : Ideal R)
    [Module.Finite R I] [Module.Flat R I] : I.IsPrincipal := by
  by_cases hI : I = ⊥
  · rw [hI]
    infer_instance
  let : Module.Free R I := Module.free_of_flat_of_finrank_eq R I 1
    (quotient_fiber_finrank R I hI)
  exact (Submodule.rank_le_one_iff_isPrincipal I).mp (ideal_rank_one R I hI).le

theorem free_of_principal (I : Ideal R) (hI : I.IsPrincipal) : Module.Free R I := by
  obtain ⟨a, ha⟩ := hI.principal
  by_cases ha0 : a = 0
  · have hi : I = ⊥ := by rw [ha, ha0, Submodule.span_zero_singleton]
    rw [hi]
    infer_instance
  exact Module.Free.of_equiv
    ((LinearEquiv.toSpanNonzeroSingleton R R a ha0).trans (LinearEquiv.ofEq _ _ ha.symm))

theorem flat_of_local_principal (I : Ideal R)
    (h : ∀ (p : Ideal R) [p.IsMaximal],
      (I.map (algebraMap R (Localization.AtPrime p))).IsPrincipal) : Module.Flat R I := by
  apply Module.flat_of_isLocalized_maximal (R := R) (S := R)
    (Mₚ := fun p _ => I.map (algebraMap R (Localization.AtPrime p)))
    (f := fun p _ => Algebra.idealMap I (S := Localization.AtPrime p))
  intro p hp
  let S := Localization.AtPrime p
  let J := I.map (algebraMap R S)
  let : Module.Free S J := free_of_principal S J (h p)
  exact (Module.flat_iff_of_isLocalization S p.primeCompl J).mp inferInstance

theorem of_local_principal [Finite (MaximalSpectrum R)] (I : Ideal R) [Module.Finite R I]
    (h : ∀ (p : Ideal R) [p.IsMaximal],
      (I.map (algebraMap R (Localization.AtPrime p))).IsPrincipal) : I.IsPrincipal := by
  let := flat_of_local_principal R I h
  exact of_flat R I

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SemilocalIdealPrincipal
