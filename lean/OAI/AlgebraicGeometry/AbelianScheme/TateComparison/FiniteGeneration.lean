import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PadicResidueTopology
import Mathlib.RingTheory.Finiteness.Basic

/-! # Finite Generation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiniteGeneration.Tate

noncomputable section

/-! Finite generation of the actual Tate module from finite first-level
torsion. Lifts of all first-level points generate to every finite precision;
compactness of their p-adic coefficient space supplies exact coefficients. -/

universe u v
variable (q : ℕ) [Fact q.Prime] {H : Type u} [AddCommGroup H]
  {I : Type v} [Fintype I]

def combination (b : I → Add.Tate.Module (H := H) q) : (I → ℤ_[q]) →ₗ[ℤ_[q]] Add.Tate.Module (H := H) q :=
  ∑ i, (LinearMap.proj i).smulRight (b i)

theorem combination_single [DecidableEq I] (b : I → Add.Tate.Module (H := H) q) (i : I) :
    combination q b (Pi.single i 1) = b i := by
  classical
  simp [combination, Pi.single_apply]

theorem combination_approximation (b : I → Add.Tate.Module (H := H) q)
    (hb : Function.Surjective (fun i => Evaluation.Tate.evaluate q 1 (b i)))
    (n : ℕ) (y : Add.Tate.Module (H := H) q) :
    ∃ c : I → ℤ_[q], ∃ z : Add.Tate.Module (H := H) q,
      y = combination q b c + (q : ℤ_[q]) ^ n • z := by
  classical
  induction n with
  | zero => exact ⟨0, y, by simp⟩
  | succ n ih =>
    obtain ⟨c, z, hz⟩ := ih
    obtain ⟨i, hi⟩ := hb (Evaluation.Tate.evaluate q 1 z)
    change Evaluation.Tate.evaluate q 1 (b i) = Evaluation.Tate.evaluate q 1 z at hi
    have he : Evaluation.Tate.evaluate q 1 (z - b i) = 0 := by rw [map_sub, hi, sub_self]
    obtain ⟨w, hw⟩ := (Evaluation.Tate.evaluate_eq_zero_iff q 1 (z - b i)).mp he
    have hz' : z = b i + (q : ℤ_[q]) • w := by
      simpa only [pow_one] using (eq_add_of_sub_eq hw.symm).trans (add_comm _ _)
    refine ⟨c + (q : ℤ_[q]) ^ n • Pi.single i 1, w, ?_⟩
    rw [hz, hz', _root_.map_add, map_smul, combination_single, smul_add, pow_succ, mul_smul]
    exact (add_assoc _ _ _).symm

theorem combination_continuous_evaluate (b : I → Add.Tate.Module (H := H) q) (n : ℕ) :
    @Continuous (I → ℤ_[q]) (Add.Tate.torsion q H n) _ ⊥
      (fun c => Evaluation.Tate.evaluate q n (combination q b c)) := by
  let : TopologicalSpace (Add.Tate.torsion q H n) := ⊥
  let : DiscreteTopology (Add.Tate.torsion q H n) := ⟨rfl⟩
  let f : (I → ZMod (q ^ n)) → Add.Tate.torsion q H n :=
    fun c => ∑ i, c i • Evaluation.Tate.evaluate q n (b i)
  have hf : Continuous f := continuous_of_discreteTopology
  have hr : Continuous (fun c : I → ℤ_[q] => fun i => PadicInt.toZModPow n (c i)) :=
    continuous_pi fun i => (PadicResidueTopology.continuous_padic_residue q n).comp (continuous_apply i)
  convert hf.comp hr using 1
  funext c
  simp only [Function.comp_apply, f, combination, LinearMap.sum_apply,
    LinearMap.smulRight_apply, LinearMap.proj_apply, map_sum, map_smul]
  rfl

theorem combination_surjective (b : I → Add.Tate.Module (H := H) q)
    (hb : Function.Surjective (fun i => Evaluation.Tate.evaluate q 1 (b i))) :
    Function.Surjective (combination q b) := by
  intro y
  let S : ℕ → Set (I → ℤ_[q]) := fun n =>
    {c | Evaluation.Tate.evaluate q n (combination q b c) = Evaluation.Tate.evaluate q n y}
  have hclosed : ∀ n, IsClosed (S n) := by
    intro n
    let : TopologicalSpace (Add.Tate.torsion q H n) := ⊥
    let : DiscreteTopology (Add.Tate.torsion q H n) := ⟨rfl⟩
    exact isClosed_singleton.preimage (combination_continuous_evaluate q b n)
  have hnonempty : ∀ n, (S n).Nonempty := by
    intro n
    obtain ⟨c, z, hz⟩ := combination_approximation q b hb n y
    refine ⟨c, ?_⟩
    change Evaluation.Tate.evaluate q n (combination q b c) = Evaluation.Tate.evaluate q n y
    rw [hz, _root_.map_add]
    have he := (Evaluation.Tate.evaluate_eq_zero_iff q n ((q : ℤ_[q]) ^ n • z)).mpr ⟨z, rfl⟩
    rw [he, add_zero]
  have hdecreasing : ∀ n, S (n + 1) ⊆ S n := by
    intro n c hc
    exact ((combination q b c).property n).symm.trans
      ((congrArg (Add.Tate.transition q n) hc).trans (y.property n))
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    S hdecreasing hnonempty (hclosed 0).isCompact hclosed
  refine ⟨c, ?_⟩
  apply Subtype.ext
  funext n
  exact Set.mem_iInter.mp hc n

theorem finite_of_finite_torsion [Finite (Add.Tate.torsion q H 1)]
    (hdiv : ∀ x : H, ∃ y, q • y = x) :
    _root_.Module.Finite ℤ_[q] (Add.Tate.Module (H := H) q) := by
  let := Fintype.ofFinite (Add.Tate.torsion q H 1)
  let b : Add.Tate.torsion q H 1 → Add.Tate.Module (H := H) q :=
    fun x => (Evaluation.Tate.evaluate_surjective q hdiv 1 x).choose
  have hb : Function.Surjective (fun i => Evaluation.Tate.evaluate q 1 (b i)) := by
    intro x
    exact ⟨x, (Evaluation.Tate.evaluate_surjective q hdiv 1 x).choose_spec⟩
  exact _root_.Module.Finite.of_surjective (combination q b) (combination_surjective q b hb)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiniteGeneration.Tate
