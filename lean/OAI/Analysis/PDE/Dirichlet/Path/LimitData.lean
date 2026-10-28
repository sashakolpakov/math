import OAI.Analysis.PDE.Dirichlet.Path.LimitProperties

open Set Module Filter
open scoped Topology BoundedContinuousFunction Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.Normed.Function.Holder

/-- A limit of actual density-path solutions, retaining its closed-domain
jet, equation, boundary values and a convergent subsequence. This records
the outcome of compactness, not an assumption of solvability. -/
structure BanachPathLimit {n : ℕ} {P V ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    (r B₀ F₀ F₁ : CoordinateSpace n 4 → ℝ)
    (hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}) (β : ℝ)
    (s : ℕ → SmoothPathSolution e lat r B₀ F₀ F₁) (t : ℝ) where
  value : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK β
  periodic : LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value value))
  boundary : ∀ x : {x | r x ≤ 0}, r x = 0 → OAI.Analysis.Normed.Function.Holder.C2Holder.value value x = B₀ x
  admissible : ∀ x : {x | r x ≤ 0},
    OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK β OAI.Analysis.Calculus.Quaternion.fourSlots value) x) =
      densityPath F₀ F₁ t x ∧
    (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK β OAI.Analysis.Calculus.Quaternion.fourSlots value) x)).PosDef
  subsequence : ℕ → ℕ
  strict : StrictMono subsequence
  converges : ∀ x : {x | r x ≤ 0},
    Tendsto (fun k ↦ B₀ x + (s (subsequence k)).u x) atTop (𝓝 (OAI.Analysis.Normed.Function.Holder.C2Holder.value value x))

end OAI.Analysis.PDE.Dirichlet
