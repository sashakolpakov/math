import OAI.Analysis.PDE.Dirichlet.Uniform.DoubleFields
import OAI.Analysis.PDE.Dirichlet.Fourth.PathTangent
import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.Subtract

noncomputable section
open Set Module Metric
open scoped ContDiff ComplexOrder
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Elliptic OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n+1) 4

/-- The uniform twice-tangential inverse estimate supplies the actual
Hessian fields required by the local interior fourth-order reduction. -/
theorem InteriorThirdPathData.uniform_remainder_double_field_bounds
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ 5 B₀)
    (hF₀ : ContDiff ℝ 3 F₀) (hF₁ : ContDiff ℝ 3 F₁)
    (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat r) (hBp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat B₀)
    (hp₀ : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat F₀) (hp₁ : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) [Nonempty {x | r x ≤ 0}]
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x) :
    OAI.Analysis.PDE.Dirichlet.UniformPeriodicDoubleFieldBounds e lat r (d.exponent/2)
      (fun s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁ => s.u) := by
  intro T W hT hW hTp hWp hTtan hWtan
  obtain ⟨M,hM,hjets⟩ := d.uniform_second_tangent_C2Holder e lat hK hr hB₀ hF₀ hF₁
    hrp hBp hp₀ hp₁ hbounded hreg hrpos hpos₀ hpos₁ T W
    (hT.of_le (by simp)) (hW.of_le (by simp)) hTp hWp hTtan hWtan
  refine ⟨M,hM,?_⟩
  intro s
  obtain ⟨U,hUn,_,_,_,hU₂⟩ := hjets s
  exact OAI.Analysis.PDE.Elliptic.hasDoubleFieldHolderBound_of_C2Holder U hUn (fun x => (hU₂ x).symm)

/-- The full nonlinear potential has a uniform local fourth-order Hölder
bound at every interior point. The radius and constant precede the solution. -/
theorem InteriorThirdPathData.interior_fourth_estimate
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ 5 B₀)
    (hF₀ : ContDiff ℝ 3 F₀) (hF₁ : ContDiff ℝ 3 F₁)
    (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat r) (hBp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat B₀)
    (hp₀ : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat F₀) (hp₁ : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) [Nonempty {x | r x ≤ 0}]
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    {a : E} (ha : r a < 0) :
    ∃ ρ > 0, ∃ C > 0, ∀ s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁,
      OAI.Analysis.PDE.Elliptic.HasFourthHolderBound (closedBall a ρ ∩ {x | r x ≤ 0}) (d.exponent/2)
        (fun y => B₀ y+s.u y) C := by
  have hfields := d.uniform_remainder_double_field_bounds e lat hK hr hB₀ hF₀ hF₁
    hrp hBp hp₀ hp₁ hbounded hreg hrpos hpos₀ hpos₁
  have hα : 0 ≤ d.exponent/2 := (half_pos d.exponent_pos).le
  have hα1 : d.exponent/2 ≤ 1 := by linarith [d.exponent_lt_one]
  obtain ⟨ρ,hρ,C,hC,hbound⟩ := hfields.interior_fourth_bound hr.continuous hrp hα
    (fun s => s.smooth) ha
  have hc : IsCompact (closedBall a ρ ∩ {x | r x ≤ 0}) :=
    (isCompact_closedBall a ρ).inter_right (isClosed_le hr.continuous continuous_const)
  obtain ⟨B,hB⟩ := OAI.Analysis.PDE.Elliptic.exists_fixed_fourth_holder hc B₀ hB₀ hα hα1
  refine ⟨ρ,hρ,C+‖B‖,add_pos_of_pos_of_nonneg hC (norm_nonneg B),?_⟩
  intro s
  have heq : (fun y => (B₀ y+s.u y)-B₀ y) = s.u := by funext y; ring
  have hsub : OAI.Analysis.PDE.Elliptic.HasFourthHolderBound (closedBall a ρ ∩ {x | r x ≤ 0}) (d.exponent/2)
      (fun y => (B₀ y+s.u y)-B₀ y) C := by
    rw [heq]
    exact hbound s
  exact OAI.Analysis.PDE.Elliptic.restored_fourth_holder ((hB₀.of_le (by norm_num)).add s.smooth)
    (hB₀.of_le (by norm_num)) hsub B hB

end OAI.Analysis.PDE.Schauder
