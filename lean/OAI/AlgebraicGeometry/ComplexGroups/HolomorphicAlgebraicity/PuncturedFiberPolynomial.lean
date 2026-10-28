import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GlobalFiberPolynomial
import Mathlib.Analysis.Normed.Module.Connected

/-! # Punctured Fiber Polynomial -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PuncturedFiberPolynomial.Constructions.Cone

noncomputable section

/-!
# Fixed-degree fiber equations over a punctured complex vector space
-/

open Set Filter _root_.Polynomial
open scoped _root_.Topology

theorem isConnected_punctured_complex_space {n : ℕ} (hn : 0 < n) :
    IsConnected ({0}ᶜ : Set (Fin n → ℂ)) := by
  apply isConnected_compl_singleton_of_one_lt_rank
  rw [← Module.finrank_eq_rank]
  have hdim : Module.finrank ℝ (Fin n → ℂ) = n * 2 := by
    simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [hdim]
  exact_mod_cast (show 1 < n * 2 by omega)

theorem exists_punctured_fiber_polynomial {n : ℕ} (hn : 0 < n)
    {S : Set ((Fin n → ℂ) × ℂ)}
    (hproper : IsProperMap (fun p : S => p.val.1))
    (hfinite : ∀ x, {z : ℂ | (x, z) ∈ S}.Finite)
    (hlocal : ∀ p ∈ S, p ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S p) :
    ∃ (d : ℕ) (P : (Fin n → ℂ) → ℂ[X]),
      (∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) {0}ᶜ) ∧
      (∀ y, y ≠ 0 → (P y).Monic ∧ (P y).natDegree = d) ∧
      ∀ x, x ≠ 0 → ∃ (V : Set (Fin n → ℂ)) (c : (Fin n → ℂ) → ℂ),
        IsOpen V ∧ x ∈ V ∧ V ⊆ {0}ᶜ ∧ DifferentiableOn ℂ c V ∧
        (¬∀ᶠ y in 𝓝 x, c y = 0) ∧ V ⊆ closure {y | y ∈ V ∧ c y ≠ 0} ∧
        ∀ y ∈ V, c y ≠ 0 → (P y).Separable ∧
          ∀ z : ℂ, (y, z) ∈ S ↔ (P y).eval z = 0 := by
  have hconn := isConnected_punctured_complex_space hn
  obtain ⟨d, P, hcoeff, hP, hnear⟩ := GlobalFiberPolynomial.Constructions.Cone.exists_global_fixed_degree_fiber_polynomial
    (S := S) isClosed_singleton.isOpen_compl hconn.isPreconnected hconn.nonempty hproper
    (fun x _ => hfinite x) (fun x hx z hp => hlocal (x, z) hp (fun hz => hx
      (show x = 0 from congrArg Prod.fst hz)))
  exact ⟨d, P, hcoeff, hP, hnear⟩

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PuncturedFiberPolynomial.Constructions.Cone
