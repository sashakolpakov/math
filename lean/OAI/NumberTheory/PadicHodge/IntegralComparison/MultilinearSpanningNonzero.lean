import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Multilinear Spanning Nonzero -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.MultilinearSpanningNonzero

noncomputable section

/-! A nonzero multilinear map is nonzero on some tuple from any
spanning family, including actual scalar-extension unit vectors. -/

open scoped TensorProduct

universe u v w z
variable {S : Type u} [CommRing S] {M : Type v} {N : Type w} {T : Type z}
  [AddCommGroup N] [Module S N] [AddCommGroup T] [Module S T]
  (η : M → N) (hη : Submodule.span S (Set.range η) = ⊤)

include hη in
theorem eq_zero : ∀ (n : ℕ) (f : MultilinearMap S (fun _ : Fin n => N) T),
    (∀ v : Fin n → M, f (fun i => η (v i)) = 0) → f = 0 := by
  intro n
  induction n with
  | zero =>
      intro f hf
      apply MultilinearMap.ext
      intro v
      change f v = 0
      have hv : v = (fun i : Fin 0 => η (Fin.elim0 i)) := Subsingleton.elim _ _
      rw [hv]
      exact hf (fun i => Fin.elim0 i)
  | succ n ih =>
      intro f hf
      apply (multilinearCurryLeftEquiv S (fun _ : Fin (n+1) => N) T).injective
      change f.curryLeft = 0
      apply LinearMap.ext_on_range hη
      intro x
      change f.curryLeft (η x) = 0
      apply ih
      intro v
      change f (Fin.cons (η x) (fun i => η (v i))) = 0
      convert hf (Fin.cons x v) using 1
      congr 1
      funext i
      exact Fin.cases rfl (fun _ => rfl) i

include hη in
theorem exists_nonzero (n : ℕ) (f : MultilinearMap S (fun _ : Fin n => N) T)
    (hf : ∃ v, f v ≠ 0) : ∃ v : Fin n → M, f (fun i => η (v i)) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hz := eq_zero η hη n f h
  obtain ⟨v, hv⟩ := hf
  exact hv (by rw [hz]; rfl)

variable {R : Type*} [CommRing R] [Algebra R S]
  {L : Type*} [AddCommGroup L] [Module R L]
  (e : S ⊗[R] L →ₗ[S] N) (he : Function.Surjective e)

include he in
theorem scalar_span : Submodule.span S (Set.range (fun x : L => e ((1 : S) ⊗ₜ[R] x))) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨t, rfl⟩ := he x
  induction t using TensorProduct.inductionOn with
  | tmul a x =>
      rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨x, rfl⟩)
  | add t u ht hu =>
      rw [map_add]
      exact Submodule.add_mem _ (ht trivial) (hu trivial)

include he in
theorem scalar_exists_nonzero (n : ℕ) (f : MultilinearMap S (fun _ : Fin n => N) T)
    (hf : ∃ v, f v ≠ 0) :
    ∃ v : Fin n → L, f (fun i => e ((1 : S) ⊗ₜ[R] v i)) ≠ 0 :=
  exists_nonzero (fun x => e ((1 : S) ⊗ₜ[R] x)) (scalar_span e he) n f hf

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.MultilinearSpanningNonzero
