import OAI.RepresentationTheory.Weil.Local.CharacterScaling
import OAI.RepresentationTheory.Weil.Local.QuadraticIntertwiner
import OAI.RepresentationTheory.Weil.Local.GaussianNonarchimedean

/-! # Quarter Turn Structure -/

namespace OAI.RepresentationTheory.Weil.Local.QuarterTurnStructure.Construction

noncomputable section

/-! A conjugate-linear symmetry when the coefficient field contains a square root of -1. -/

open _root_.MeasureTheory
open scoped ComplexConjugate

theorem schwartzBruhat_conjugate_mem {k : Type} [NormedField k] {n : ℕ}
    {f : FunctionsMetaplectic.Construction.Position k n → ℂ} (hf : f ∈ FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    (fun x => conj (f x)) ∈ FunctionsMetaplectic.Construction.schwartzBruhat k n := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with hf | ⟨d, e, φ, rfl⟩
      · exact FunctionsMetaplectic.Construction.compact_locallyConstant_mem (hf.1.comp _) (hf.2.comp_left (map_zero _))
      · exact FunctionsMetaplectic.Construction.schwartz_coordinate_mem e (φ.postcompCLM Complex.conjCLE.toContinuousLinearMap)
  | zero => simpa only [Pi.zero_apply, map_zero] using! (FunctionsMetaplectic.Construction.schwartzBruhat k n).zero_mem
  | add f g _ _ hf hg =>
      simpa only [Pi.add_apply, map_add] using! (FunctionsMetaplectic.Construction.schwartzBruhat k n).add_mem hf hg
  | smul c f _ hf =>
      simpa only [Pi.smul_apply, smul_eq_mul, map_mul] using! (FunctionsMetaplectic.Construction.schwartzBruhat k n).smul_mem (conj c) hf

theorem quarterTurn_ne_zero {k : Type} [Field k] {r : k} (hr : r ^ 2 = -1) : r ≠ 0 := by
  intro h
  rw [h, zero_pow (by decide)] at hr
  exact (neg_ne_zero.mpr (one_ne_zero : (1 : k) ≠ 0)) hr.symm

def quarterTurnStructure {k : Type} [NormedField k] {n : ℕ}
    (r : k) (hr : r ^ 2 = -1) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) : FunctionsMetaplectic.Construction.schwartzBruhat k n :=
  ⟨fun x => conj (f.val (r • x)),
    schwartzBruhat_conjugate_mem (FunctionsMetaplectic.Construction.schwartzBruhat_coordinateEquiv
      (CharacterScaling.Construction.scalarPositionEquiv n r (quarterTurn_ne_zero hr)).toContinuousAddEquiv f).property⟩

theorem quarterTurnStructure_smul {k : Type} [NormedField k] {n : ℕ}
    (r : k) (hr : r ^ 2 = -1) (c : ℂ) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    quarterTurnStructure r hr (c • f) = conj c • quarterTurnStructure r hr f := by
  apply Subtype.ext
  funext x
  exact map_mul (starRingEnd ℂ) c (f.val (r • x))

theorem quarterTurnStructure_neg {k : Type} [NormedField k] {n : ℕ}
    (r : k) (hr : r ^ 2 = -1) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    quarterTurnStructure r hr (-f) = -quarterTurnStructure r hr f := by
  apply Subtype.ext
  funext x
  exact map_neg (starRingEnd ℂ) (f.val (r • x))

theorem quarterTurnStructure_quadratic {k : Type} [NormedField k] {n : ℕ}
    (r : k) (hr : r ^ 2 = -1) (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1)
    (hmem : ∀ B (f : FunctionsMetaplectic.Construction.schwartzBruhat k n), FunctionsMetaplectic.Construction.quadraticOperator ψ B f.val ∈ FunctionsMetaplectic.Construction.schwartzBruhat k n)
    (B : Matrix (Fin n) (Fin n) k) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    QuadraticIntertwiner.Construction.testQuadratic ψ hmem B (quarterTurnStructure r hr f) =
      quarterTurnStructure r hr (QuadraticIntertwiner.Construction.testQuadratic ψ hmem B f) := by
  apply Subtype.ext
  funext x
  change ψ (FunctionsMetaplectic.Construction.quadratic B x) * conj (f.val (r • x)) =
    conj (ψ (FunctionsMetaplectic.Construction.quadratic B (r • x)) * f.val (r • x))
  rw [QuadraticIntertwiner.Construction.quadratic_smul_vector, hr, neg_one_mul, GaussianNonarchimedean.Construction.unitary_character_neg ψ hu, map_mul,
    starRingEnd_self_apply]

theorem haarModulus_quarterTurn {k : Type} [NormedField k] [LocallyCompactSpace k]
    (r : k) (hr : r ^ 2 = -1) : DeterminantMeasure.Construction.haarModulus k r = 1 := by
  apply (pow_eq_one_iff_of_nonneg (show 0 ≤ DeterminantMeasure.Construction.haarModulus k r from zero_le) (by decide : (4 : ℕ) ≠ 0)).mp
  rw [← map_pow]
  have h4 : r ^ 4 = 1 := by
    calc
      _ = (r ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hr]; ring
  rw [h4, map_one]

theorem dot_quarterTurn {k : Type} [Field k] {n : ℕ} (r : k) (hr : r ^ 2 = -1)
    (x y : FunctionsMetaplectic.Construction.Position k n) : FunctionsMetaplectic.Construction.dot (r • x) (r • y) = -FunctionsMetaplectic.Construction.dot x y := by
  simp only [FunctionsMetaplectic.Construction.dot, Pi.smul_apply, smul_eq_mul, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = r ^ 2 * (x i * y i) := by ring
    _ = _ := by rw [hr, neg_one_mul]

theorem fourier_quarterTurnStructure
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
    (r : k) (hr : r ^ 2 = -1) (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1)
    (μ : Measure k) [μ.IsAddHaarMeasure] (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) (quarterTurnStructure r hr f).val x =
      conj (FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f.val (r • x)) := by
  let g : FunctionsMetaplectic.Construction.Position k n → ℂ := fun z => conj (f.val z) * ψ (FunctionsMetaplectic.Construction.dot (r • x) z)
  have h := CharacterScaling.Construction.integral_scalar_position n r (quarterTurn_ne_zero hr) μ g
  rw [haarModulus_quarterTurn r hr] at h
  simp only [NNReal.coe_one, one_pow, inv_one, one_smul] at h
  calc
    _ = ∫ y, g (r • y) ∂Measure.pi (fun _ : Fin n => μ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        change conj (f.val (r • y)) * ψ (-FunctionsMetaplectic.Construction.dot x y) = conj (f.val (r • y)) * ψ (FunctionsMetaplectic.Construction.dot (r • x) (r • y))
        rw [dot_quarterTurn r hr]
    _ = ∫ y, g y ∂Measure.pi (fun _ : Fin n => μ) := h
    _ = _ := by
      rw [FunctionsMetaplectic.Construction.fourierIntegral, ← integral_conj]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        change conj (f.val y) * ψ (FunctionsMetaplectic.Construction.dot (r • x) y) = conj (f.val y * ψ (-FunctionsMetaplectic.Construction.dot (r • x) y))
        rw [map_mul, GaussianNonarchimedean.Construction.unitary_character_neg ψ hu, starRingEnd_self_apply]

end

end OAI.RepresentationTheory.Weil.Local.QuarterTurnStructure.Construction
