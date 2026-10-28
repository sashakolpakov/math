import OAI.Analysis.PDE.Dirichlet.Boundary.InverseClosedRegularity

noncomputable section
open Set Module Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Schauder

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace (n+1) 4
local instance inverseFamilyFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance inverseFamilyFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance inverseFamilySecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseFamilySecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseFamilyThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseFamilyThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseFamilyC2Group {Ω D : Set E} (hΩD : Ω ⊆ D) (α : ℝ) :
    NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance
local instance inverseFamilyC2Space {Ω D : Set E} (hΩD : Ω ⊆ D) (α : ℝ) :
    NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance

def HasC3CompactLimit
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (s : ℕ → SmoothPathSolution e lat r B₀ F₀ F₁) : Prop :=
    ∃ (φ : ℕ → ℕ) (g : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK (d.exponent/2)) (ψ : E → ℝ),
      StrictMono φ ∧
      Tendsto (fun k => OAI.Analysis.Normed.Function.Holder.C2Holder.lowerHalf d.exponent_pos.le (d.jets (s (φ k)))) atTop (𝓝 g) ∧
      ContDiff ℝ 3 ψ ∧ LatticePeriodic e lat ψ ∧
      LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value g)) ∧
      (∀ x : {x | r x ≤ 0},
        OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK (d.exponent/2) OAI.Analysis.Calculus.Quaternion.fourSlots g) x =
          quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) ∧
      (∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)

theorem InteriorThirdPathData.exists_C3_compact_limit
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrper : LatticePeriodic e lat r) (hBper : LatticePeriodic e lat B₀)
    (hp₀ : LatticePeriodic e lat F₀) (hp₁ : LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) (hne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    (s : ℕ → SmoothPathSolution e lat r B₀ F₀ F₁) : HasC3CompactLimit e lat d s := by
  obtain ⟨t,ht,σ,hσ,hσlim⟩ := isCompact_Icc.tendsto_subseq (fun k => (s k).parameter)
  obtain ⟨L,hLlim⟩ := OAI.Analysis.PDE.Dirichlet.InteriorThirdPathData.exists_banach_limit_with_norm_convergence
    (n := n) (hΩK := hΩK) e lat hK d
    (hr.of_le (by simp)) hB₀ hF₀ hF₁ hrper hBper hbounded hreg hpos₀ hpos₁
    (fun k => s (σ k)) (t := t) ht hσlim
  have hthird := L.contDiffOn_three_fixed_data e lat hK d hr hB₀ hF₀ hF₁
    hrper hBper hp₀ hp₁ hbounded hne hreg hpos₀ hpos₁
  obtain ⟨ψ,hψ,hψp,hfield,hpos⟩ := L.exists_C3_positive_representative
    (by omega) e lat hK hr hrper hbounded hreg hthird
  exact ⟨σ ∘ L.subsequence,L.value,ψ,hσ.comp L.strict,hLlim,hψ,hψp,L.periodic,hfield,hpos⟩

end OAI.Analysis.PDE.Dirichlet
