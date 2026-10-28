import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.Data.ENat.BigOperators

/-! # Smith Determinant -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SmithDeterminant

noncomputable section

/-! The length of a full-rank lattice quotient is the order of the
determinant of its inclusion, first in the actual Smith normal form bases. -/

open _root_.Module
open scoped Classical

universe u v w

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {M : Type v} [AddCommGroup M] [Module R M] {ι : Type w} [Fintype ι]

omit [IsPrincipalIdealRing R] [Fintype ι] in
theorem ord_prod (s : Finset ι) (a : ι → R) (ha : ∀ i ∈ s, a i ≠ 0) :
    Ring.ord R (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord R (a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Ring.ord_mul R (mem_nonZeroDivisors_of_ne_zero
        (Finset.prod_ne_zero_iff.mpr (fun j hj => ha j (Finset.mem_insert_of_mem hj)))),
      ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))]

theorem quotient_length (N : Submodule R M) (b : Basis ι R M)
    (h : Module.finrank R N = Module.finrank R M) :
    Module.length R (M ⧸ N) = ∑ i, Ring.ord R (Submodule.smithNormalFormCoeffs b h i) := by
  rw [(N.quotientEquivPiSpan b h).length_eq, Module.length_pi_of_fintype]
  rfl

theorem smith_matrix (N : Submodule R M) (b : Basis ι R M)
    (h : Module.finrank R N = Module.finrank R M) :
    LinearMap.toMatrix (Submodule.smithNormalFormBotBasis b h)
      (Submodule.smithNormalFormTopBasis b h) N.subtype =
        Matrix.diagonal (Submodule.smithNormalFormCoeffs b h) := by
  ext i j
  simp only [LinearMap.toMatrix_apply, Submodule.subtype_apply,
    Submodule.smithNormalFormBotBasis_def, map_smul, Finsupp.smul_apply, Basis.repr_self]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

theorem quotient_length_smith_det (N : Submodule R M) (b : Basis ι R M)
    (h : Module.finrank R N = Module.finrank R M) :
    Module.length R (M ⧸ N) = Ring.ord R
      (LinearMap.toMatrix (Submodule.smithNormalFormBotBasis b h)
        (Submodule.smithNormalFormTopBasis b h) N.subtype).det := by
  rw [smith_matrix R N b h, Matrix.det_diagonal, ord_prod,
    quotient_length R N b h]
  intro i _
  exact Submodule.smithNormalFormCoeffs_ne_zero b h i

omit [IsDomain R] [IsPrincipalIdealRing R] in
theorem ord_matrix_basis_change {N : Type*} [AddCommGroup N] [Module R N]
    (b b' : Basis ι R M) (c c' : Basis ι R N) (f : M →ₗ[R] N) :
    Ring.ord R (LinearMap.toMatrix b c f).det =
      Ring.ord R (LinearMap.toMatrix b' c' f).det := by
  have h : LinearMap.toMatrix b c f =
      LinearMap.toMatrix c' c (LinearMap.id : N →ₗ[R] N) *
        LinearMap.toMatrix b' c' f *
          LinearMap.toMatrix b b' (LinearMap.id : M →ₗ[R] M) := by
    rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
    simp
  have hb : IsUnit (LinearMap.toMatrix b b' (LinearMap.id : M →ₗ[R] M)).det :=
    (LinearEquiv.refl R M).isUnit_det b b'
  have hc : IsUnit (LinearMap.toMatrix c' c (LinearMap.id : N →ₗ[R] N)).det :=
    (LinearEquiv.refl R N).isUnit_det c' c
  rw [h, Matrix.det_mul, Matrix.det_mul,
    Ring.ord_mul_of_isUnit_right hb, Ring.ord_mul_of_isUnit_left hc]

theorem quotient_length_det (N : Submodule R M) (b : Basis ι R M)
    (c : Basis ι R N) :
    Module.length R (M ⧸ N) = Ring.ord R (LinearMap.toMatrix c b N.subtype).det := by
  have h : Module.finrank R N = Module.finrank R M := by
    rw [Module.finrank_eq_card_basis c, Module.finrank_eq_card_basis b]
  rw [quotient_length_smith_det R N b h,
    ord_matrix_basis_change R (Submodule.smithNormalFormBotBasis b h) c
      (Submodule.smithNormalFormTopBasis b h) b]

theorem cokernel_length_matrix {N : Type*} [AddCommGroup N] [Module R N]
    (b : Basis ι R M) (c : Basis ι R N) (f : M →ₗ[R] N)
    (hf : Function.Injective f) :
    Module.length R (N ⧸ f.range) = Ring.ord R (LinearMap.toMatrix b c f).det := by
  let e := LinearEquiv.ofInjective f hf
  let b' := b.map e
  have he : LinearMap.toMatrix b' c f.range.subtype = LinearMap.toMatrix b c f := by
    ext i j
    simp [LinearMap.toMatrix_apply, b', e]
  rw [quotient_length_det R f.range c b', he]

theorem cokernel_length_det (b : Basis ι R M) (f : M →ₗ[R] M)
    (hf : Function.Injective f) :
    Module.length R (M ⧸ f.range) = Ring.ord R f.det := by
  rw [cokernel_length_matrix R b b f hf, LinearMap.det_toMatrix]

theorem quotient_length_ne_top (N : Submodule R M) (b : Basis ι R M)
    (c : Basis ι R N) : Module.length R (M ⧸ N) ≠ ⊤ := by
  have h : Module.finrank R N = Module.finrank R M := by
    rw [Module.finrank_eq_card_basis c, Module.finrank_eq_card_basis b]
  rw [quotient_length R N b h]
  apply ENat.sum_ne_top.mpr
  intro i _
  exact Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero
    (Submodule.smithNormalFormCoeffs_ne_zero b h i))

theorem cokernel_length_ne_top {N : Type*} [AddCommGroup N] [Module R N]
    (b : Basis ι R M) (c : Basis ι R N) (f : M →ₗ[R] N)
    (hf : Function.Injective f) : Module.length R (N ⧸ f.range) ≠ ⊤ :=
  quotient_length_ne_top R f.range c (b.map (LinearEquiv.ofInjective f hf))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SmithDeterminant
