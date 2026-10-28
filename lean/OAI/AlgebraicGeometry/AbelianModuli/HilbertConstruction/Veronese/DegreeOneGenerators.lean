import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.SubalgebraGeneratorLifts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.VeroneseFiniteGeneration

/-! # Degree One Generators -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.DegreeOneGenerators

noncomputable section

/-! The constructed balanced Veronese algebra has finitely many
internal degree-one generators, indexed by a nonempty finite ordinal. -/
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

theorem veronese_degree_one_generators
    (g : ℕ → Submodule R A) [GradedAlgebra g] (N : ℕ) (F : Finset A)
    (hF : ∀ x ∈ F, x ∈ g N)
    (hgen : Algebra.adjoin R (F : Set A) = Subalgebra.veroneseSubalgebra g N) :
    ∃ (n : ℕ) (D : Fin (n + 1) → Subalgebra.veroneseSubalgebra g N),
      (∀ j, D j ∈ Grading.veroneseGrading g N 1) ∧ Algebra.adjoin R (Set.range D) = ⊤ := by
  let V := Subalgebra.veroneseSubalgebra g N
  have hFV (x) (hx : x ∈ F) : x ∈ V :=
    Subalgebra.veronese_homogeneous_mem g N 1 (by simpa only [Nat.mul_one] using hF x hx)
  let e : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm
  let L := Finite.SubalgebraGeneratorLifts.finiteSubalgebraGeneratorLift V F hFV
  let D : Fin (Fintype.card F + 1) → V := Fin.cons 0 (fun j => L (e j))
  refine ⟨Fintype.card F, D, ?_, ?_⟩
  · intro j
    refine Fin.cases ((Grading.veroneseGrading g N 1).zero_mem) (fun k => ?_) j
    change (e k).val ∈ g (N * 1)
    simpa only [Nat.mul_one] using hF (e k).val (e k).property
  · apply top_le_iff.mp
    rw [← Finite.SubalgebraGeneratorLifts.finiteSubalgebraGeneratorLift_adjoin V F hFV hgen]
    apply Algebra.adjoin_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨(e.symm j).succ, by simp only [D, L, Fin.cons_succ, Equiv.apply_symm_apply]⟩

theorem balancedDeterminant_veronese_degree_one_generators
    (R : Type u) [CommRing R] {r m : ℕ} (hr : 0 < r) (i : Fin m) :
    ∃ N : ℕ, 0 < N ∧ ∃ (n : ℕ)
      (D : Fin (n + 1) → Subalgebra.veroneseSubalgebra (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i) N),
      (∀ j, D j ∈ Grading.veroneseGrading (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i) N 1) ∧
      Algebra.adjoin R (Set.range D) = ⊤ := by
  obtain ⟨N, hN, F, hF, hgen⟩ := Balanced.VeroneseFiniteGeneration.balancedDeterminant_veronese_finite_generation R hr i
  obtain ⟨n, D, hD, hg⟩ := veronese_degree_one_generators (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i) N F hF hgen
  exact ⟨N, hN, n, D, hD, hg⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.DegreeOneGenerators
