import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ImmersionNormalForm
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! # Submersion Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SubmersionCoordinates.Constructions

noncomputable section

/-!
# DegreeTwo: analytic submersion coordinates preserving the actual equation

The implicit function theorem supplies a local biholomorphic coordinate
change whose first coordinate is exactly the given complex function.
-/

open scoped ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- An analytic complex-valued submersion is itself a normal coordinate;
both directions of the local coordinate change are analytic. -/
theorem exists_analytic_submersion_coordinates (f : E → ℂ) (x : E)
    (hf : ContDiffAt ℂ ω f x) (hs : Function.Surjective (fderiv ℂ f x)) :
    ∃ q : OpenPartialHomeomorph E (ℂ × (fderiv ℂ f x).ker),
      x ∈ q.source ∧ q x = (f x, 0) ∧
      (∀ y, (q y).1 = f y) ∧
      ContDiffOn ℂ ω q q.source ∧ ContDiffOn ℂ ω q.symm q.target := by
  let d := fderiv ℂ f x
  have hd : d.range = ⊤ := LinearMap.range_eq_top.mpr hs
  have hstrict := hf.hasStrictFDerivAt (by simp)
  let hker := d.ker_closedComplemented_of_finiteDimensional_range
  let D := hstrict.implicitFunctionDataOfComplemented f d hd hker
  let q₀ := D.toOpenPartialHomeomorph
  have hright : ContDiffAt ℂ ω D.rightFun x := by
    change ContDiffAt ℂ ω (fun y => Classical.choose hker (y - x)) x
    exact (Classical.choose hker).contDiff.contDiffAt.comp x
      (contDiffAt_id.sub contDiffAt_const)
  have hq : ContDiffAt ℂ ω q₀ x := hf.prodMk hright
  have hqi : ContDiffAt ℂ ω q₀.symm (q₀ x) :=
    D.contDiffAt_implicitFunction hf hright (by simp)
  refine ⟨q₀.restrContDiff ℂ ω (by simp), ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨D.pt_mem_toOpenPartialHomeomorph_source, hq, hqi⟩
  · change (f x, Classical.choose hker (x - x)) = (f x, 0)
    rw [sub_self, map_zero]
  · intro y
    rfl
  · exact q₀.contDiffOn_restrContDiff_source ℂ (by simp)
  · exact q₀.contDiffOn_restrContDiff_target ℂ (by simp)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SubmersionCoordinates.Constructions
