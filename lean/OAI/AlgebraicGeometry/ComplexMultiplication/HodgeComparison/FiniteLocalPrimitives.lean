import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Intersection
import OAI.AlgebraicTopology.Cohomology.Singular.ChartBalls
import Mathlib.Topology.ShrinkingLemma

/-! # Finite Local Primitives -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FiniteLocalPrimitives.CM.Construction

noncomputable section

/-! Finite families of genuine closed one-forms admit simultaneous
smooth primitives on neighborhoods of each point. -/

open Set _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem restrict_local_primitive {U V : Opens M} (hUV : U ≤ V)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1) (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E V 0)
    (hf : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f = Intersection.CM.Construction.restrictSmoothForm V 1 a) :
    ∃ g : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E U 0, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d g = Intersection.CM.Construction.restrictSmoothForm U 1 a := by
  let i : U → V := fun x => ⟨x.val, hUV x.property⟩
  have hi : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ i := by
    rw [← ContMDiff.subtypeVal_comp_iff]
    exact contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ∞)
  refine ⟨Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback i hi f, ?_⟩
  rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_pullback, hf]
  unfold Intersection.CM.Construction.restrictSmoothForm
  rw [← Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_comp]
  rfl

theorem finite_family_local_primitives [FiniteDimensional ℝ E] {ι : Type*} [Finite ι]
    (a : ι → Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 1) (x : M) :
    ∃ U : Opens M, x ∈ U ∧
      ∃ f : ι → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E U 0,
        ∀ i, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (f i) = Intersection.CM.Construction.restrictSmoothForm U 1 (a i).val := by
  classical
  choose U hx f hf using fun i => Intersection.CM.Construction.exists_local_intrinsic_primitive (a i) x
  let W : Opens M := ⨅ i, U i
  have hxW : x ∈ W := by
    change x ∈ ((⨅ i, U i : Opens M) : Set M)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hx
  have h (i : ι) := restrict_local_primitive (E := E) (M := M)
    (show W ≤ U i from iInf_le U i) (a i).val (f i) (hf i)
  choose g hg using h
  exact ⟨W, hxW, g, hg⟩

/-- The primitive neighborhood can also be chosen contractible, so actual
singular cocycles admit primitives on the same neighborhood. -/
theorem finite_family_contractible_local_primitives [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι] (a : ι → Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 1) (x : M) :
    ∃ U : Opens M, x ∈ U ∧ ContractibleSpace U ∧
      ∃ f : ι → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E U 0,
        ∀ i, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (f i) = Intersection.CM.Construction.restrictSmoothForm U 1 (a i).val := by
  classical
  obtain ⟨V, hx, f, hf⟩ := finite_family_local_primitives a x
  obtain ⟨U, hxU, hUV, hc⟩ := AlgebraicTopology.Cohomology.Singular.ChartBalls.exists_contractible_open_subset_of_mem_nhds
    E x (V.isOpen.mem_nhds hx)
  choose g hg using fun i => restrict_local_primitive hUV (a i).val (f i) (hf i)
  exact ⟨U, hxU, hc, g, hg⟩

/-- A finite primitive cover with compact cores lying inside the primitive
domains. The cores still cover the entire compact manifold. -/
theorem finite_primitive_cover [FiniteDimensional ℝ E] [CompactSpace M] [T2Space M]
    {ι : Type*} [Finite ι] (a : ι → Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 1) :
    ∃ (s : Finset M) (U V : s → Opens M),
      (∀ j, ContractibleSpace (U j)) ∧
      (∀ x : M, ∃ j, x ∈ V j) ∧
      (∀ j, closure (V j : Set M) ⊆ U j) ∧
      (∀ j, IsCompact (closure (V j : Set M))) ∧
      ∃ f : ∀ j, ι → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E (U j) 0,
        ∀ j i, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (f j i) = Intersection.CM.Construction.restrictSmoothForm (U j) 1 (a i).val := by
  classical
  choose U hx hc f hf using finite_family_contractible_local_primitives a
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (U x : Set M)) (fun x => (U x).isOpen) (by
      intro x _
      exact mem_iUnion.mpr ⟨x, hx x⟩)
  have hcover : (univ : Set M) ⊆ ⋃ j : s, (U j.val : Set M) := by
    intro x hx'
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hs hx')
    exact mem_iUnion.mpr ⟨⟨j, hj⟩, hxj⟩
  obtain ⟨v, hv, hvo, hvU, hvc⟩ := exists_subset_iUnion_closure_subset_t2space
    isCompact_univ (fun j : s => (U j.val).isOpen)
    (fun _ _ => Set.toFinite _) hcover
  refine ⟨s, fun j => U j.val, fun j => ⟨v j, hvo j⟩, fun j => hc j.val, ?_, hvU, hvc,
    fun j => f j.val, fun j => hf j.val⟩
  intro x
  exact mem_iUnion.mp (hv (mem_univ x))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FiniteLocalPrimitives.CM.Construction
