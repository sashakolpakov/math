import OAI.Analysis.Normed.Function.Holder.ScalarExtensionMap
import OAI.Analysis.Normed.Function.Holder.ScalarExtensionSymmetry
import OAI.Analysis.Normed.Function.Holder.C2HolderLattice

open Set Module
open scoped BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder

open OAI.Analysis.PDE.Dirichlet

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

omit [Fintype ι] in
/-- Hölder data on a periodic domain admit a bounded global extension with
the same Hölder norm and the same physical lattice periodicity. -/
theorem exists_periodic_scalar_holder_extension
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set E} [Nonempty K]
    (hK : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x ↦ x ∈ K))
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (f : HolderMap K ℝ α)
    (hf : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value f))) :
    ∃ g : HolderMap E ℝ α, ‖g‖ ≤ ‖f‖ ∧
      OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.HolderMap.value g) ∧
      (∀ y : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value g y = OAI.Analysis.Normed.Function.Holder.HolderMap.value f y) := by
  obtain ⟨g, hgn, hg, hgf⟩ := exists_scalar_holder_extension hα hα1 f
  refine ⟨g, hgn, ?_, hgf⟩
  intro x l
  rw [OAI.Analysis.PDE.Dirichlet.lattice_translate_eq, hg, hg]
  let t : E := e.symm ((l : P), 0)
  have hmem (y : E) : t + y ∈ K ↔ y ∈ K := by
    apply Iff.of_eq
    simpa only [t, OAI.Analysis.PDE.Dirichlet.lattice_translate_eq] using hK y l
  let σ : K ≃ K :=
    { toFun := fun y ↦ ⟨t + y, (hmem y).mpr y.property⟩
      invFun := fun y ↦ ⟨-t + y, (hmem (-t + y)).mp (by simp)⟩
      left_inv := fun y ↦ Subtype.ext (by simp)
      right_inv := fun y ↦ Subtype.ext (by simp) }
  have hσ (y : K) : (σ y : E) = (IsometryEquiv.addLeft t) y := rfl
  have hfv (y : K) : OAI.Analysis.Normed.Function.Holder.HolderMap.value f (σ y) = OAI.Analysis.Normed.Function.Holder.HolderMap.value f y := by
    have hy := hf y l
    rw [OAI.Analysis.PDE.Dirichlet.lattice_translate_eq] at hy
    change boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value f) (t + y) =
      boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value f) y at hy
    rw [boundedZeroExtension_apply _ ((hmem y).mpr y.property),
      boundedZeroExtension_apply _ y.property] at hy
    exact hy
  exact boundedHolderExtension_isometry (OAI.Analysis.Normed.Function.Holder.HolderMap.value f) ‖f‖ ‖f‖ α
    (IsometryEquiv.addLeft t) σ hσ hfv x

end OAI.Analysis.Normed.Function.Holder
