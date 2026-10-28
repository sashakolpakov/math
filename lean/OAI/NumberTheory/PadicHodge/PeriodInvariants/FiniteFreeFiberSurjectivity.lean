import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-! # Finite Free Fiber Surjectivity -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteFreeFiberSurjectivity

noncomputable section

/-! # An endomorphism of a finite free module is invertible if every residue-field fibre is -/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M)

theorem isUnit_det
    (hf : ∀ (m : Ideal R) [m.IsMaximal], Function.Surjective (f.baseChange (R ⧸ m))) :
    IsUnit f.det := by
  apply Ideal.span_singleton_eq_top.mp
  by_contra hn
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {f.det}) hn
  have : m.IsMaximal := hm
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  let e := LinearEquiv.ofBijective (f.baseChange (R ⧸ m))
    ⟨LinearMap.injective_iff_surjective.mpr (hf m), hf m⟩
  have hu : IsUnit (LinearMap.det (f.baseChange (R ⧸ m))) := e.isUnit_det'
  rw [LinearMap.det_baseChange] at hu
  have hz : algebraMap R (R ⧸ m) f.det = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (Set.mem_singleton _)))
  exact hu.ne_zero hz

theorem bijective
    (hf : ∀ (m : Ideal R) [m.IsMaximal], Function.Surjective (f.baseChange (R ⧸ m))) :
    Function.Bijective f := by
  have he := (LinearMap.equivOfIsUnitDet (isUnit_det f hf)).bijective
  simpa only [Function.Bijective, Function.Injective, Function.Surjective,
    LinearMap.equivOfIsUnitDet_apply] using he

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteFreeFiberSurjectivity
