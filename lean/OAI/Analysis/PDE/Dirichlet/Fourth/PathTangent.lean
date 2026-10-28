import OAI.Analysis.PDE.Dirichlet.Fourth.PathExponent
import OAI.Analysis.PDE.Dirichlet.Fourth.TangentSolver

/-! Uniform true fourth-order tangential jets, obtained without a fourth-order
Hölder hypothesis on the solution. -/
noncomputable section
open Set Module
open scoped ContDiff ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Elliptic

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]
local notation "E" => CoordinateSpace (n+1) 4
attribute [local instance] uniformClassicalFirstGroup uniformClassicalFirstSpace
  uniformClassicalSecondGroup uniformClassicalSecondSpace

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V] in
theorem _root_.OAI.Analysis.PDE.Schauder.InteriorThirdPathData.uniform_second_tangent_C2Holder_of_classical_estimate
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ 5 B₀)
    (hF₀ : ContDiff ℝ 3 F₀) (hF₁ : ContDiff ℝ 3 F₁)
    (hrp : LatticePeriodic e lat r) (hBp : LatticePeriodic e lat B₀)
    (hp₀ : LatticePeriodic e lat F₀) (hp₁ : LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) [Nonempty {x | r x ≤ 0}]
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (_ : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    (T S : E → E) (hT : ContDiff ℝ 4 T) (hS : ContDiff ℝ 4 S)
    (hTp : LatticePeriodic e lat T) (hSp : LatticePeriodic e lat S)
    (hTtan : ∀ x, r x=0 → fderiv ℝ r x (T x)=0)
    (hStan : ∀ x, r x=0 → fderiv ℝ r x (S x)=0)
    (hclassical : ∃ C > 0, UniformPathClassicalEstimate e lat d C) :
    ∃ M > 0, ∀ s : SmoothPathSolution e lat r B₀ F₀ F₁,
      ∃ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK (d.exponent/2),
        ‖U‖ ≤ M ∧ U ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat ∧
        (∀ x : {x | r x ≤ 0}, OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative s.u T) S x = OAI.Analysis.Normed.Function.Holder.C2Holder.value U x) ∧
        (∀ x : {x | r x ≤ 0},
          fderiv ℝ (OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative s.u T) S) x = OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x) ∧
        (∀ x : {x | r x ≤ 0},
          fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative s.u T) S)) x =
            OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x) := by
  obtain ⟨B,hB,hsource⟩ := d.uniform_second_background_forcing_half (by omega) e lat hK hr
    hB₀ hF₀ hF₁ hrp hBp hp₀ hp₁ hbounded
    (by obtain ⟨x⟩ := (inferInstance : Nonempty {x | r x ≤ 0}); exact ⟨x,x.property⟩)
    hreg hpos₀ hpos₁ T S hT hS hTp hSp
  obtain ⟨C,hC,hsolve⟩ := hclassical
  exact OAI.Analysis.PDE.Dirichlet.UniformPathClassicalEstimate.uniform_second_tangent
    (n := n) (e := e) (lat := lat) (r := r) (B₀ := B₀) (F₀ := F₀) (F₁ := F₁)
    (hΩK := hΩK) (d := d) (C := C) (B := B) hsolve hC hB
    (hr.of_le (by simp)) hreg (hB₀.of_le (by norm_num))
    (hF₀.of_le (by norm_num)) (hF₁.of_le (by norm_num)) T S
    (hT.of_le (by norm_num)) (hS.of_le (by norm_num)) hTp hSp hTtan hStan hsource

theorem _root_.OAI.Analysis.PDE.Schauder.InteriorThirdPathData.uniform_second_tangent_C2Holder
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ 5 B₀)
    (hF₀ : ContDiff ℝ 3 F₀) (hF₁ : ContDiff ℝ 3 F₁)
    (hrp : LatticePeriodic e lat r) (hBp : LatticePeriodic e lat B₀)
    (hp₀ : LatticePeriodic e lat F₀) (hp₁ : LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) [Nonempty {x | r x ≤ 0}]
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    (T S : E → E) (hT : ContDiff ℝ 4 T) (hS : ContDiff ℝ 4 S)
    (hTp : LatticePeriodic e lat T) (hSp : LatticePeriodic e lat S)
    (hTtan : ∀ x, r x=0 → fderiv ℝ r x (T x)=0)
    (hStan : ∀ x, r x=0 → fderiv ℝ r x (S x)=0) :
    ∃ M > 0, ∀ s : SmoothPathSolution e lat r B₀ F₀ F₁,
      ∃ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK (d.exponent/2),
        ‖U‖ ≤ M ∧ U ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat ∧
        (∀ x : {x | r x ≤ 0}, OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative s.u T) S x = OAI.Analysis.Normed.Function.Holder.C2Holder.value U x) ∧
        (∀ x : {x | r x ≤ 0},
          fderiv ℝ (OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative s.u T) S) x = OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x) ∧
        (∀ x : {x | r x ≤ 0},
          fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative s.u T) S)) x =
            OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x) := by
  apply d.uniform_second_tangent_C2Holder_of_classical_estimate (n := n) e lat hK hr hB₀ hF₀ hF₁
    hrp hBp hp₀ hp₁ hbounded hreg hrpos hpos₀ hpos₁ T S hT hS hTp hSp hTtan hStan
  exact OAI.Analysis.PDE.Dirichlet.InteriorThirdPathData.uniform_classical_estimate (n := n) e lat hK d hr
    (hB₀.of_le (by norm_num)) (hF₀.of_le (by norm_num)) (hF₁.of_le (by norm_num))
    hrp hBp hp₀ hp₁ hbounded hreg hrpos hpos₀ hpos₁

end OAI.Analysis.PDE.Dirichlet
