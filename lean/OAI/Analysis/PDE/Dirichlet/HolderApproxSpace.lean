import OAI.Analysis.PDE.Dirichlet.IndexedHolderApprox

open Set Module Filter
open scoped Topology ContDiff BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

omit [Fintype ι] in
theorem latticePeriodic_restriction_zeroExtension
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set E}
    (hK : LatticePeriodic e lat (fun x ↦ x ∈ K))
    (f : E → ℝ) (hf : LatticePeriodic e lat f) (g : K →ᵇ ℝ)
    (hg : ∀ x : K, g x = f x) : LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension g) := by
  intro x l
  have hm := Iff.of_eq (hK x l)
  by_cases hx : x ∈ K
  · rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply g (hm.mpr hx), OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply g hx, hg, hg]
    exact hf x l
  · have hy := mt hm.mp hx
    simp only [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension, zeroExtend, dite_eq_right hx, dite_eq_right hy]

omit [Fintype ι] in
/-- Smooth data are uniformly dense in the lattice-periodic Hölder codomain,
with a uniform bound in the original exponent. No false density assertion
in the full Hölder norm is used. -/
theorem exists_bounded_smooth_latticeHolder_approximation {m : ℕ}
    (L : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m))
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set E} [Nonempty K] (hK : LatticePeriodic e lat (fun x ↦ x ∈ K))
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (f : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := K) (α := α) e lat) :
    ∃ (F : ℕ → E → ℝ) (φ : ℕ → OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := K) (α := α) e lat),
      (∀ j, ContDiff ℝ ∞ (F j)) ∧ (∀ j, LatticePeriodic e lat (F j)) ∧
      (∀ j, ‖φ j‖ ≤ ‖f‖) ∧
      (∀ j (x : K), OAI.Analysis.Normed.Function.Holder.HolderMap.value (φ j).val x = F j x) ∧
      TendstoUniformly (fun j ↦ OAI.Analysis.Normed.Function.Holder.HolderMap.value (φ j).val) (OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val) atTop := by
  obtain ⟨F, hFs, hFp, hFB, hFH, hFlim⟩ :=
    exists_isometric_periodic_smooth_holder_approximation L e lat hK hα hα1 f.val f.property
  let G (j : ℕ) : K →ᵇ ℝ := OAI.Analysis.Normed.Function.Holder.boundedRestriction (F j) (hFs j).continuous.continuousOn ‖f.val‖
    (fun x _ ↦ by simpa only [Real.norm_eq_abs] using hFB j x)
  have hGH (j : ℕ) (x y : K) : ‖G j x - G j y‖ ≤ ‖f.val‖ * dist x y ^ α := by
    change ‖F j x - F j y‖ ≤ ‖f.val‖ * dist (x : E) (y : E) ^ α
    simpa only [Real.norm_eq_abs] using hFH j x y
  let φ₀ (j : ℕ) : OAI.Analysis.Normed.Function.Holder.HolderMap K ℝ α := OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα.le (G j) (hGH j)
  have hφper (j : ℕ) : φ₀ j ∈ OAI.Analysis.Normed.Function.Holder.latticeHolder e lat :=
    latticePeriodic_restriction_zeroExtension e lat hK (F j) (hFp j) (G j) (fun _ ↦ rfl)
  let φ (j : ℕ) : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := K) (α := α) e lat := ⟨φ₀ j, hφper j⟩
  refine ⟨F, φ, hFs, hFp, ?_, fun _ _ ↦ rfl, hFlim⟩
  intro j
  change ‖φ₀ j‖ ≤ ‖f.val‖
  apply OAI.Analysis.Normed.Function.Holder.HolderMap.norm_le_of_bounds hα.le (norm_nonneg f.val)
  · intro x
    change ‖F j x‖ ≤ ‖f.val‖
    simpa only [Real.norm_eq_abs] using hFB j x
  · exact hGH j

end OAI.Analysis.PDE.Dirichlet
