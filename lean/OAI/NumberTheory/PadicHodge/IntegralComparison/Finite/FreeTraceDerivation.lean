import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.Derivation.Basic

/-! # Free Trace Derivation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FreeTraceDerivation

noncomputable section

/-! Finite free algebra trace commutes with compatible derivations.
The proof differentiates multiplication matrices and cancels the trace
of the change-of-frame commutator. -/

universe u v w z

variable {R : Type u} {A : Type v} {B : Type w} {ι : Type z}
  [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B]
  [Fintype ι] (b : Module.Basis ι A B)
  (D : Derivation R A A) (E : Derivation R B B)
  (h : ∀ a : A, E (algebraMap A B a) = algebraMap A B (D a))

include h in
theorem derivation_smul (a : A) (x : B) :
    E (a • x) = D a • x + a • E x := by
  simp only [Algebra.smul_def, E.leibniz, h, Algebra.algebraMap_self_apply]
  ring

include h in
theorem coordinate_derivation (x : B) (i : ι) :
    b.repr (E x) i = D (b.repr x i) +
      ∑ j, b.repr x j * b.repr (E (b j)) i := by
  classical
  calc
    b.repr (E x) i = b.coord i (E (∑ j, b.repr x j • b j)) :=
      congrArg (fun y => b.repr (E y) i) (b.sum_repr x).symm
    _ = ∑ j, (D (b.repr x j) * b.repr (b j) i +
        b.repr x j * b.repr (E (b j)) i) := by
      simp only [map_sum, derivation_smul D E h, map_add, map_smul,
        smul_eq_mul, Module.Basis.coord_apply]
    _ = D (b.repr x i) + ∑ j, b.repr x j * b.repr (E (b j)) i := by
      rw [Finset.sum_add_distrib]
      simp only [Module.Basis.repr_self_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem coordinate_mul (x y : B) (i : ι) :
    b.repr (x * y) i = ∑ j, b.repr y j * b.repr (x * b j) i := by
  calc
    b.repr (x * y) i = b.coord i (x * ∑ j, b.repr y j • b j) :=
      congrArg (fun z => b.repr (x * z) i) (b.sum_repr y).symm
    _ = ∑ j, b.repr y j * b.repr (x * b j) i := by
      simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
        smul_eq_mul, Module.Basis.coord_apply]

theorem trace_eq_sum (x : B) :
    Algebra.trace A B x = ∑ i, b.repr (x * b i) i := by
  classical
  rw [Algebra.trace_eq_matrix_trace b]
  simp only [Matrix.trace, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]

include b h in
theorem trace_derivation (x : B) :
    Algebra.trace A B (E x) = D (Algebra.trace A B x) := by
  classical
  have hi (i : ι) : b.repr (x * E (b i)) i + b.repr (E x * b i) i =
      D (b.repr (x * b i) i) +
        ∑ j, b.repr (x * b i) j * b.repr (E (b j)) i := by
    have he := coordinate_derivation b D E h (x * b i) i
    rw [E.leibniz] at he
    simpa only [smul_eq_mul, map_add, Finsupp.add_apply, mul_comm (b i) (E x)] using he
  have hs := congrArg (fun z : ι → A => ∑ i, z i) (funext hi)
  simp only [Finset.sum_add_distrib] at hs
  have hc : (∑ i, b.repr (x * E (b i)) i) =
      ∑ i, ∑ j, b.repr (x * b i) j * b.repr (E (b j)) i := by
    calc
      (∑ i, b.repr (x * E (b i)) i) =
          ∑ i, ∑ j, b.repr (E (b i)) j * b.repr (x * b j) i :=
        Finset.sum_congr rfl (fun i _ => coordinate_mul b x (E (b i)) i)
      _ = ∑ i, ∑ j, b.repr (x * b i) j * b.repr (E (b j)) i := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact mul_comm _ _
  rw [hc] at hs
  have ht : (∑ i, b.repr (E x * b i) i) = ∑ i, D (b.repr (x * b i) i) := by
    exact add_left_cancel (hs.trans (add_comm _ _))
  simpa only [trace_eq_sum b, map_sum] using ht

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FreeTraceDerivation
