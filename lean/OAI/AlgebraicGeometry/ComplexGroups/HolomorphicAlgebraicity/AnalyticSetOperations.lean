import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Fin.Tuple.Basic

/-! # Analytic Set Operations -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity

noncomputable section

/-!
# Basic operations on local holomorphic zero sets
-/

open Set

theorem AnalyticSetOperations.Constructions.Cone.holomorphicZeroSetAt_of_not_mem_closed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {S : Set E} (hS : IsClosed S) {x : E} (hx : x ∉ S) :
    ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S x := by
  refine ⟨Sᶜ, hS.isOpen_compl, hx, 1, fun _ _ => 1,
    fun _ => differentiableOn_const _, ?_⟩
  intro y hy
  constructor
  · intro h
    exact False.elim (hy h)
  · intro h
    exact False.elim (one_ne_zero (h 0))

theorem ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt.inter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {S T : Set E} {x : E} (hS : ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S x) (hT : ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt T x) :
    ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (S ∩ T) x := by
  obtain ⟨U, hU, hxU, m, f, hf, hSf⟩ := hS
  obtain ⟨V, hV, hxV, n, g, hg, hTg⟩ := hT
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, m + n, Fin.append f g, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using (hf j).mono (show U ∩ V ⊆ U from inter_subset_left)
    · simpa only [Fin.append_right] using (hg j).mono (show U ∩ V ⊆ V from inter_subset_right)
  · intro y hy
    rw [mem_inter_iff, hSf y hy.1, hTg y hy.2]
    constructor
    · rintro ⟨hfy, hgy⟩ i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [Fin.append_left] using hfy j
      · simpa only [Fin.append_right] using hgy j
    · intro h
      exact ⟨fun i => by simpa only [Fin.append_left] using h (Fin.castAdd n i),
        fun j => by simpa only [Fin.append_right] using h (Fin.natAdd m j)⟩

theorem AnalyticSetOperations.Constructions.Cone.holomorphicZeroSetAt_zero_fiber
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {g : E → F} {U : Set E} (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    {x : E} (hx : x ∈ U) : ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt {y | g y = 0} x := by
  let e := (Module.finBasis ℂ F).equivFunL
  refine ⟨U, hU, hx, Module.finrank ℂ F, (fun i y => e (g y) i), ?_, ?_⟩
  · intro i
    exact (differentiable_apply i).comp_differentiableOn
      (e.differentiable.comp_differentiableOn hg)
  · intro y _
    change g y = 0 ↔ ∀ i, e (g y) i = 0
    constructor
    · intro h i
      rw [h, map_zero]
      rfl
    · intro h
      apply e.injective
      ext i
      simpa only [map_zero, Pi.zero_apply] using h i

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity
