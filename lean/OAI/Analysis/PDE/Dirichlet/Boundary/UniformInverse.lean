import OAI.Analysis.PDE.Dirichlet.Boundary.InverseFamilyCompactness
import OAI.Analysis.PDE.Dirichlet.Boundary.InverseOperator
import OAI.Analysis.PDE.Dirichlet.Uniform.InverseCompactness

noncomputable section
open Set Module Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Schauder

def IsCompactLowerFamily {X Y I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (A : I → X →L[ℝ] Y) : Prop :=
  ∀ i : ℕ → I, ∃ (φ : ℕ → ℕ) (L : X →L[ℝ] Y) (C : ℝ),
    StrictMono φ ∧ 0 ≤ C ∧ (∀ x, ‖x‖ ≤ C*‖L x‖) ∧
      Tendsto (fun k => A (i (φ k))) atTop (𝓝 L)

def HasLowerOperatorLimit {X Y I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (A : I → X →L[ℝ] Y) (i : ℕ → I) : Prop :=
  ∃ (φ : ℕ → ℕ) (L : X →L[ℝ] Y) (C : ℝ),
    StrictMono φ ∧ 0 ≤ C ∧ (∀ x, ‖x‖ ≤ C*‖L x‖) ∧
      Tendsto (fun k => A (i (φ k))) atTop (𝓝 L)

theorem HasLowerOperatorLimit.of_continuous
    {X Y I Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [TopologicalSpace Z]
    (A : Z → X →L[ℝ] Y) (f : I → Z) (i : ℕ → I)
    (φ : ℕ → ℕ) (z : Z) (hφ : StrictMono φ)
    (hlim : Tendsto (fun k => f (i (φ k))) atTop (𝓝 z))
    (hA : Continuous A) (hb : ∃ C > 0, ∀ x, ‖x‖ ≤ C * ‖A z x‖) :
    HasLowerOperatorLimit (fun j => A (f j)) i := by
  obtain ⟨C,hC,hb⟩ := hb
  exact ⟨φ,A z,C,hφ,hC.le,hb,(hA.tendsto z).comp hlim⟩

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]
local notation "E" => CoordinateSpace (n+1) 4
local instance uniformInverseFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance uniformInverseFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance uniformInverseSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance uniformInverseSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance uniformInverseC2Group {Ω D : Set E} (hΩD : Ω ⊆ D) (α : ℝ) :
    NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance
local instance uniformInverseC2Space {Ω D : Set E} (hΩD : Ω ⊆ D) (α : ℝ) :
    NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance
local instance uniformInverseC2Module {Ω D : Set E} (hΩD : Ω ⊆ D) (α : ℝ) :
    Module ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance
local instance uniformInverseC2Bounded {Ω D : Set E} (hΩD : Ω ⊆ D) (α : ℝ) :
    IsBoundedSMul ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := NormedSpace.toIsBoundedSMul
local instance uniformInverseC2Continuous {Ω D : Set E} (hΩD : Ω ⊆ D) (α : ℝ) :
    ContinuousSMul ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := IsBoundedSMul.continuousSMul

def pathMooreLinearization
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (s : SmoothPathSolution e lat r B₀ F₀ F₁) :
    OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := d.exponent/2) e lat →L[ℝ]
      OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} ℝ (d.exponent/2) :=
  restrictedMooreDerivative hΩK (div_nonneg d.exponent_pos.le (by norm_num)) e lat
    (OAI.Analysis.Normed.Function.Holder.C2Holder.lowerHalf d.exponent_pos.le (d.jets s))

def UniformRestrictedInverseBound
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK) (C : ℝ) : Prop :=
  ∀ (s : SmoothPathSolution e lat r B₀ F₀ F₁)
      (u : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := d.exponent/2) e lat),
      ‖u‖ ≤ C * ‖restrictedMooreDerivative hΩK (div_nonneg d.exponent_pos.le (by norm_num)) e lat
        (OAI.Analysis.Normed.Function.Holder.C2Holder.lowerHalf d.exponent_pos.le (d.jets s)) u‖

theorem HasC3CompactLimit.lower_operator_limit
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (hr : ContDiff ℝ ∞ r) (hrper : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    [Nonempty {x | r x ≤ 0}]
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (seq : ℕ → SmoothPathSolution e lat r B₀ F₀ F₁)
    (hcompact : HasC3CompactLimit e lat d seq) :
    HasLowerOperatorLimit (pathMooreLinearization e lat d) seq := by
  have hβ : 0 < d.exponent/2 := div_pos d.exponent_pos (by norm_num)
  have hβ1 : d.exponent/2 < 1 := by linarith [d.exponent_lt_one]
  obtain ⟨φ,g,ψ,hφ,hlim,hψ,hψp,hgp,hfield,hpos⟩ := hcompact
  have hb := restrictedMooreDerivative_bounded_below (n := n+1) (hΩD := hΩK)
    (by omega) e lat hK hr hrper hbounded hreg hrpos hβ hβ1 g hgp ψ hψ hψp hpos hfield
  exact OAI.Analysis.PDE.Dirichlet.HasLowerOperatorLimit.of_continuous
    (restrictedMooreDerivative hΩK hβ.le e lat)
    (fun s => OAI.Analysis.Normed.Function.Holder.C2Holder.lowerHalf d.exponent_pos.le (d.jets s)) seq φ g hφ hlim
    (continuous_restrictedMooreDerivative hΩK hβ.le e lat) hb

/-- A common inverse estimate for all retained path solutions. The compactness
argument uses the proved third-order bound, rather than a supplied inverse bound. -/
theorem InteriorThirdPathData.compact_lower_path_linearization
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrper : LatticePeriodic e lat r) (hBper : LatticePeriodic e lat B₀)
    (hp₀ : LatticePeriodic e lat F₀) (hp₁ : LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    [Nonempty {x | r x ≤ 0}]
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x) :
    IsCompactLowerFamily (pathMooreLinearization e lat d) := by
  have hne : {x | r x ≤ 0}.Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty {x | r x ≤ 0})
    exact ⟨x,x.property⟩
  intro seq
  exact OAI.Analysis.PDE.Dirichlet.HasC3CompactLimit.lower_operator_limit e lat hK d hr hrper hbounded hreg hrpos seq
    (OAI.Analysis.PDE.Dirichlet.InteriorThirdPathData.exists_C3_compact_limit e lat hK d hr hB₀ hF₀ hF₁
      hrper hBper hp₀ hp₁ hbounded hne hreg hpos₀ hpos₁ seq)

theorem InteriorThirdPathData.uniform_restricted_inverse_bound
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrper : LatticePeriodic e lat r) (hBper : LatticePeriodic e lat B₀)
    (hp₀ : LatticePeriodic e lat F₀) (hp₁ : LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    [Nonempty {x | r x ≤ 0}]
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x) :
    ∃ C > 0, UniformRestrictedInverseBound e lat d C := by
  exact uniform_lower_bound_of_subsequence_lower_bound (pathMooreLinearization e lat d)
    (OAI.Analysis.PDE.Dirichlet.InteriorThirdPathData.compact_lower_path_linearization e lat hK d hr hB₀ hF₀ hF₁
      hrper hBper hp₀ hp₁ hbounded hreg hrpos hpos₀ hpos₁)

end OAI.Analysis.PDE.Dirichlet
