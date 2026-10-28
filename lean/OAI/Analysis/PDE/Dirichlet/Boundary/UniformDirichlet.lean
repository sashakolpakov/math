import OAI.Analysis.PDE.Dirichlet.Boundary.UniformInverse
import OAI.Analysis.PDE.Dirichlet.Boundary.InverseEstimate

noncomputable section
open Set Module Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Schauder

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]
local notation "E" => CoordinateSpace (n+1) 4
local instance uniformDirichletFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance uniformDirichletFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance uniformDirichletSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance uniformDirichletSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def UniformPathMooreSolvability
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK) (C : ℝ) : Prop :=
  ∀ (s : SmoothPathSolution e lat r B₀ F₀ F₁)
    (f : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := {x | r x ≤ 0}) (α := d.exponent/2) e lat),
    ∃ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK (d.exponent/2), ‖U‖ ≤ C*‖f‖ ∧
      U ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat ∧
      ∀ x : {x | r x ≤ 0},
        OAI.LinearAlgebra.Moore.mooreDifferential (n+1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B₀ y+s.u y) x)
          (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK (d.exponent/2) OAI.Analysis.Calculus.Quaternion.fourSlots U) x) =
            OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val x

theorem InteriorThirdPathData.uniform_moore_dirichlet_solvability
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
    ∃ C > 0, UniformPathMooreSolvability e lat d C := by
  obtain ⟨C,hC,hbound⟩ := OAI.Analysis.PDE.Dirichlet.InteriorThirdPathData.uniform_restricted_inverse_bound
    e lat hK d hr hB₀ hF₀ hF₁ hrper hBper hp₀ hp₁ hbounded hreg hrpos hpos₀ hpos₁
  refine ⟨C,hC,?_⟩
  intro s f
  have hψ : ContDiff ℝ 3 (fun y => B₀ y+s.u y) := (hB₀.add s.smooth).of_le (by norm_num)
  have hψpos := quaternionHessian_posDef_on_regular_sublevel
    (hr.of_le (by simp)) hreg (hψ.of_le (by norm_num))
    (contDiff_densityPath hF₀ hF₁ s.t).continuous
    (fun x hx => densityPath_pos (hpos₀ x hx) (hpos₁ x hx) s.parameter)
    s.positive s.equation
  apply moore_solution_estimate_of_restricted_bound (hΩD := hΩK)
    (by omega) e lat hK hr hrper hbounded hreg hrpos
    (div_pos d.exponent_pos (by norm_num)) (by linarith [d.exponent_lt_one])
    (OAI.Analysis.Normed.Function.Holder.C2Holder.lowerHalf d.exponent_pos.le (d.jets s)) C (hbound s)
    (fun y => B₀ y+s.u y) hψ (hBper.add s.periodic) hψpos _ f
  intro x
  exact quaternionHessianField_eq_of_secondDerivative_eq OAI.Analysis.Calculus.Quaternion.fourSlots
    (OAI.Analysis.Normed.Function.Holder.C2Holder.lowerHalf d.exponent_pos.le (d.jets s)) _ x (d.jet_second s x)

end OAI.Analysis.PDE.Dirichlet
