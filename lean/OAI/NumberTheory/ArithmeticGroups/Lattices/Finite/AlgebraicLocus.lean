import Mathlib

/-! # Algebraic Locus -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.AlgebraicLocus.Construction

noncomputable section

/-! A finite algebraic locus over an algebraically closed field stays
finite over every extension field. -/

open scoped Classical
open _root_.MvPolynomial

theorem zeroLocus_coordinate_mem_base_image
    {k K σ : Type*} [Field k] [IsAlgClosed k] [Field K] [Algebra k K] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) (hI : (zeroLocus k I).Finite)
    {x : σ → K} (hx : x ∈ zeroLocus K I) (i : σ) :
    x i ∈ (algebraMap k K) '' ((fun y : σ → k => y i) '' zeroLocus k I) := by
  let T := (hI.image (fun y : σ → k => y i)).toFinset
  let p : MvPolynomial σ k := ∏ c ∈ T, (X i - C c)
  have hp : p ∈ I.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := k)]
    intro y hy
    dsimp only [p]
    simp only [map_prod, map_sub, aeval_X, aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
    have hyT : y i ∈ T := (hI.image (fun y : σ → k => y i)).mem_toFinset.mpr ⟨y, hy, rfl⟩
    exact Finset.prod_eq_zero hyT (sub_self _)
  have he := (radical_le_vanishingIdeal_zeroLocus (K := K) I hp) x hx
  change aeval x p = 0 at he
  dsimp only [p] at he
  simp only [map_prod, map_sub, aeval_X, aeval_C] at he
  obtain ⟨c, hc, hcx⟩ := Finset.prod_eq_zero_iff.mp he
  exact ⟨c, (hI.image (fun y : σ → k => y i)).mem_toFinset.mp hc, (sub_eq_zero.mp hcx).symm⟩

theorem finite_zeroLocus_field_extension
    {k K σ : Type*} [Field k] [IsAlgClosed k] [Field K] [Algebra k K] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) (hI : (zeroLocus k I).Finite) :
    (zeroLocus K I).Finite := by
  let S : σ → Set K := fun i => (algebraMap k K) '' ((fun y : σ → k => y i) '' zeroLocus k I)
  have hS (i : σ) : (S i).Finite := (hI.image (fun y => y i)).image (algebraMap k K)
  apply (Set.Finite.pi' hS).subset
  intro x hx i
  exact zeroLocus_coordinate_mem_base_image I hI hx i

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.AlgebraicLocus.Construction
