import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ClosedEvaluation
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Nontrivial

/-! # Closed Tensor Domain -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ClosedTensorDomain

noncomputable section

/-! Tensor products of domains over an algebraically closed field are domains
when the first factor is of finite type. The proof specializes two nonzero
coordinates simultaneously at a rational point. -/

open scoped Classical TensorProduct

variable {K R S : Type*} [Field K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S]

def evaluate (f : R →ₐ[K] K) : R ⊗[K] S →ₐ[K] S :=
  Algebra.TensorProduct.lift ((Algebra.ofId K S).comp f) (AlgHom.id K S)
    (fun _ _ => Commute.all _ _)

theorem coordinate {ι : Type*} (b : Module.Basis ι K S) (f : R →ₐ[K] K)
    (z : R ⊗[K] S) (i : ι) :
    b.repr (evaluate f z) i = f (TensorProduct.equivFinsuppOfBasisRight b z i) := by
  induction z using TensorProduct.inductionOn with
  | tmul r s =>
    simp only [evaluate, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
      Algebra.ofId_apply, AlgHom.id_apply, ← Algebra.smul_def,
      map_smul, Finsupp.smul_apply, smul_eq_mul,
      TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    exact mul_comm _ _
  | add z w hz hw => simp only [map_add, Finsupp.add_apply, hz, hw]

theorem noZeroDivisors [IsAlgClosed K] [IsDomain R] [IsDomain S]
    [Algebra.FiniteType K R] : NoZeroDivisors (R ⊗[K] S) := by
  let b := Module.Free.chooseBasis K S
  let e := TensorProduct.equivFinsuppOfBasisRight (M := R) b
  refine ⟨fun {x y} hxy => ?_⟩
  by_contra h
  push Not at h
  obtain ⟨hx, hy⟩ := h
  have hxe : e x ≠ 0 := fun hh => hx (e.injective (by simpa using hh))
  have hye : e y ≠ 0 := fun hh => hy (e.injective (by simpa using hh))
  obtain ⟨i, hi⟩ : ∃ i, e x i ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hxe (Finsupp.ext hh)
  obtain ⟨j, hj⟩ : ∃ j, e y j ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hye (Finsupp.ext hh)
  obtain ⟨f, hf⟩ := ClosedEvaluation.exists_nonzero K R (e x i * e y j)
    (mul_ne_zero hi hj)
  have hfx : evaluate f x ≠ 0 := by
    intro hh
    have hc := coordinate b f x i
    rw [hh, map_zero, Finsupp.zero_apply] at hc
    exact hf (by rw [map_mul, ← hc, zero_mul])
  have hfy : evaluate f y ≠ 0 := by
    intro hh
    have hc := coordinate b f y j
    rw [hh, map_zero, Finsupp.zero_apply] at hc
    exact hf (by rw [map_mul, ← hc, mul_zero])
  exact (mul_ne_zero hfx hfy) (by rw [← map_mul, hxy, map_zero])

theorem isDomain [IsAlgClosed K] [IsDomain R] [IsDomain S]
    [Algebra.FiniteType K R] : IsDomain (R ⊗[K] S) := by
  let : NoZeroDivisors (R ⊗[K] S) := noZeroDivisors
  exact NoZeroDivisors.to_isDomain _

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ClosedTensorDomain
