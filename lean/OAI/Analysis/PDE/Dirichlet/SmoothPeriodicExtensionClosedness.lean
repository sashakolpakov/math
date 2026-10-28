import OAI.Analysis.PDE.Dirichlet.SmoothPeriodicExtensionSequential
import Mathlib.Topology.Sequences

/-! The actual solvable parameter set is closed once the explicit
uniform higher-derivative estimates are supplied. -/

noncomputable section
open Set Module Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

def smoothPathParameterSet
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    (r B₀ F₀ F₁ : CoordinateSpace n 4 → ℝ) : Set ℝ :=
  Set.range (fun S : SmoothPathSolution e b r B₀ F₀ F₁ => S.t)

theorem smoothPathParameterSet_subset
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    (r B₀ F₀ F₁ : CoordinateSpace n 4 → ℝ) :
    smoothPathParameterSet e b r B₀ F₀ F₁ ⊆ Icc (0 : ℝ) 1 := by
  rintro t ⟨S, rfl⟩
  exact S.parameter

local notation "E" => CoordinateSpace (n+1) 4
local instance closedFirstGroup (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedAddCommGroup (X →L[ℝ] ℝ) := inferInstance
local instance closedFirstSpace (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedSpace ℝ (X →L[ℝ] ℝ) := inferInstance
local instance closedSecondGroup (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedAddCommGroup (X →L[ℝ] X →L[ℝ] ℝ) := inferInstance
local instance closedSecondSpace (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedSpace ℝ (X →L[ℝ] X →L[ℝ] ℝ) := inferInstance
local instance closedThirdGroup (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedAddCommGroup (X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ) := inferInstance
local instance closedThirdSpace (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedSpace ℝ (X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ) := inferInstance
local instance closedFourthGroup (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedAddCommGroup (X →L[ℝ] X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ) := inferInstance
local instance closedFourthSpace (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedSpace ℝ (X →L[ℝ] X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ) := inferInstance

theorem isClosed_smoothPathParameterSet_of_higher_bounds
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} (hr : ContDiff ℝ ∞ r)
    (hB₀ : ContDiff ℝ 4 B₀) (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrp : LatticePeriodic e b r) (hBp : LatticePeriodic e b B₀)
    (hp₀ : LatticePeriodic e b F₀) (hp₁ : LatticePeriodic e b F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) (hne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    (hbase : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hdet : ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet (n+1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x) = 0)
    (hconvex : ∀ x, r x ≤ 0 →
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin (n+1)) (Fin (n+1)) Q))).PosSemidef)
    {γ C₃ C₄ M₃ M₄ : ℝ} (hγ : 0 < γ) (hM₃ : 0 ≤ M₃) (hM₄ : 0 ≤ M₄)
    (h₃ : ∀ S : SmoothPathSolution e b r B₀ F₀ F₁, ∀ x, r x ≤ 0 →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+S.u y))) x‖ ≤ M₃)
    (h₄ : ∀ S : SmoothPathSolution e b r B₀ F₀ F₁, ∀ x, r x ≤ 0 →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+S.u y)))) x‖ ≤ M₄)
    (hholder₃ : ∀ S : SmoothPathSolution e b r B₀ F₀ F₁, ∀ x, r x ≤ 0 → ∀ y, r y ≤ 0 →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+S.u z))) x -
        fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+S.u z))) y‖ ≤ C₃*dist x y^γ)
    (hholder₄ : ∀ S : SmoothPathSolution e b r B₀ F₀ F₁, ∀ x, r x ≤ 0 → ∀ y, r y ≤ 0 →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+S.u z)))) x -
        fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+S.u z)))) y‖ ≤ C₄*dist x y^γ) :
    IsClosed (smoothPathParameterSet e b r B₀ F₀ F₁) := by
  classical
  apply IsSeqClosed.isClosed
  intro ts t hts hlim
  have ht : t ∈ Icc (0 : ℝ) 1 := isClosed_Icc.mem_of_tendsto hlim
    (Eventually.of_forall (fun j => smoothPathParameterSet_subset e b r B₀ F₀ F₁ (hts j)))
  change ∀ j, ∃ S : SmoothPathSolution e b r B₀ F₀ F₁, S.t = ts j at hts
  choose s hs using hts
  have hsli : Tendsto (fun j => (s j).t) atTop (𝓝 t) := by
    simpa only [hs] using hlim
  exact exists_smoothPathSolution_of_parameter_limit e b hK hr hB₀ hF₀ hF₁ hrp hBp hp₀ hp₁
    hbounded hne hreg hr₀ hpos₀ hpos₁ hbase hdet hconvex s ht hsli hγ hM₃ hM₄
    (fun j => h₃ (s j)) (fun j => h₄ (s j))
    (fun j => hholder₃ (s j)) (fun j => hholder₄ (s j))

end OAI.Analysis.PDE.Dirichlet
