import OAI.Analysis.HodgeTheory.Decomposition.Projectors

/-! # Manifold Form Filtration -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ManifoldFormFiltration.Hodge

noncomputable section

section

/-! The finite type projectors act on genuine smooth forms on any complex
manifold. Their chart values are the original algebraic covector projectors. -/

open scoped BigOperators _root_.Manifold ContDiff

open OAI.Analysis.HodgeTheory.Decomposition.Projectors.Constructions

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

def pureFormsInDegree (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n) :
    Submodule ℂ (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :=
  i.property ▸ Analysis.DifferentialForms.Manifold.ManifoldBidegree.pureManifoldFormSubmodule E M i.val.1 i.val.2

def manifoldTypeProjection (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n) :
    Module.End ℂ (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :=
  Analysis.HodgeTheory.Decomposition.Projectors.Constructions.spectralProjector Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction Analysis.HodgeTheory.Decomposition.Types.Constructions.inverseTypeCharacter
    (Analysis.HodgeTheory.Decomposition.Types.Constructions.inverseTypeCharacter_injective n) i

def manifoldChartEval (n : ℕ) (e : OpenPartialHomeomorph M E) (y : E) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n →ₗ[ℂ] (E [⋀^Fin n]→ₗ[ℝ] ℂ) where
  toFun a := (a.val.inChart e y).toAlternatingMap
  map_add' a b := by ext v; rfl
  map_smul' c a := by ext v; rfl

theorem manifoldChartEval_action (n : ℕ) (e : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) (y : E) (hy : y ∈ e.target) (z : ℂˣ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    manifoldChartEval E M n e y (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction z a) =
      Analysis.HodgeTheory.Decomposition.Projectors.Constructions.algebraicAction E n z (manifoldChartEval E M n e y a) := by
  change ((Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z a.val).inChart e y).toAlternatingMap = _
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction_inChart z a.val e he hy]
  rfl

theorem manifoldTypeProjection_inChart (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (y : E) (hy : y ∈ e.target) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    manifoldChartEval E M n e y (manifoldTypeProjection E M n i a) =
      Analysis.HodgeTheory.Decomposition.Projectors.Constructions.spectralProjector (Analysis.HodgeTheory.Decomposition.Projectors.Constructions.algebraicAction E n) Analysis.HodgeTheory.Decomposition.Types.Constructions.inverseTypeCharacter
        (Analysis.HodgeTheory.Decomposition.Types.Constructions.inverseTypeCharacter_injective n) i (manifoldChartEval E M n e y a) :=
  Analysis.HodgeTheory.Decomposition.Projectors.Constructions.spectralProjector_intertwine Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction Analysis.HodgeTheory.Decomposition.Types.Constructions.inverseTypeCharacter
    (Analysis.HodgeTheory.Decomposition.Types.Constructions.inverseTypeCharacter_injective n) (Analysis.HodgeTheory.Decomposition.Projectors.Constructions.algebraicAction E n)
    (manifoldChartEval E M n e y) (manifoldChartEval_action E M n e he y hy) i a

omit [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem mem_pureFormsInDegree_iff_chart (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    a ∈ pureFormsInDegree E M n i ↔
      ∀ e ∈ atlas E M, ∀ y ∈ e.target,
        manifoldChartEval E M n e y a ∈ Analysis.HodgeTheory.Decomposition.Pointwise.Constructions.algebraicPureSpace E n i := by
  rcases i with ⟨⟨p, q⟩, h⟩
  subst n
  rfl

theorem manifoldTypeProjection_pure [FiniteDimensional ℝ E] (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    manifoldTypeProjection E M n i a ∈ pureFormsInDegree E M n i := by
  rw [mem_pureFormsInDegree_iff_chart]
  intro e he y hy
  rw [manifoldTypeProjection_inChart E M n i e he y hy]
  exact Analysis.HodgeTheory.Decomposition.Projectors.Constructions.spectralProjector_mem _ Analysis.HodgeTheory.Decomposition.Types.Constructions.inverseTypeCharacter (Analysis.HodgeTheory.Decomposition.Types.Constructions.inverseTypeCharacter_injective n)
    (Analysis.HodgeTheory.Decomposition.Pointwise.Constructions.algebraicPureSpace E n) (Analysis.HodgeTheory.Decomposition.Projectors.Constructions.algebraicPureSpace_eigen E n)
    (Analysis.HodgeTheory.Decomposition.Pointwise.Constructions.algebraicPureSpace_span E n) i _

theorem manifoldChartEval_jointly_injective (n : ℕ)
    (a b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (h : ∀ e ∈ atlas E M, ∀ y ∈ e.target,
      manifoldChartEval E M n e y a = manifoldChartEval E M n e y b) : a = b := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  let e := chartAt E x
  have he : e ∈ atlas E M := chart_mem_atlas E x
  have hx : x ∈ e.source := mem_chart_source E x
  have hc : a.val.inChart e (e x) = b.val.inChart e (e x) := by
    ext v
    exact congrArg (fun f : E [⋀^Fin n]→ₗ[ℝ] ℂ => f v) (h e he (e x) (e.map_source hx))
  have hv := congrArg (fun f => f.compContinuousLinearMap (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e x)) hc
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_comp_chartTangentMap _ e he hx,
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_comp_chartTangentMap _ e he hx] at hv
  exact hv

theorem sum_manifoldTypeProjection [FiniteDimensional ℝ E]
    (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    (∑ i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n, manifoldTypeProjection E M n i a) = a := by
  apply manifoldChartEval_jointly_injective
  intro e he y hy
  rw [map_sum]
  simp_rw [manifoldTypeProjection_inChart E M n _ e he y hy]
  exact Analysis.HodgeTheory.Decomposition.Projectors.Constructions.sum_spectralProjector _ Analysis.HodgeTheory.Decomposition.Types.Constructions.inverseTypeCharacter (Analysis.HodgeTheory.Decomposition.Types.Constructions.inverseTypeCharacter_injective n)
    (Analysis.HodgeTheory.Decomposition.Pointwise.Constructions.algebraicPureSpace E n) (Analysis.HodgeTheory.Decomposition.Projectors.Constructions.algebraicPureSpace_eigen E n)
    (Analysis.HodgeTheory.Decomposition.Pointwise.Constructions.algebraicPureSpace_span E n) _

theorem pureFormsInDegree_iSup [FiniteDimensional ℝ E] (n : ℕ) :
    (⨆ i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n, pureFormsInDegree E M n i) = ⊤ := by
  apply top_unique
  intro a _
  rw [← sum_manifoldTypeProjection E M n a]
  apply Submodule.sum_mem
  intro i _
  exact le_iSup (pureFormsInDegree E M n) i (manifoldTypeProjection_pure E M n i a)

end

/-! The actual smooth Hodge filtration on any finite-dimensional complex
manifold, with exact type-projection criteria and degree bounds. -/

open scoped BigOperators _root_.Manifold ContDiff

open OAI.Analysis.HodgeTheory.Decomposition.Projectors.Constructions

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

theorem pureFormsInDegree_action (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) (ha : a ∈ pureFormsInDegree E M n i) (z : ℂˣ) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction z a = Analysis.HodgeTheory.Decomposition.Types.Constructions.inverseTypeCharacter i z • a := by
  apply manifoldChartEval_jointly_injective
  intro e he y hy
  rw [manifoldChartEval_action E M n e he y hy, map_smul]
  exact Analysis.HodgeTheory.Decomposition.Projectors.Constructions.algebraicPureSpace_eigen E n i _
    ((mem_pureFormsInDegree_iff_chart E M n i a).mp ha e he y hy) z

theorem manifoldTypeProjection_identity (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) (ha : a ∈ pureFormsInDegree E M n i) :
    manifoldTypeProjection E M n i a = a :=
  Analysis.HodgeTheory.Decomposition.Projectors.Constructions.spectralProjector_identity _ _ _ i a (pureFormsInDegree_action E M n i a ha)

theorem manifoldTypeProjection_other (n : ℕ) (i j : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n) (hij : i ≠ j)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) (ha : a ∈ pureFormsInDegree E M n j) :
    manifoldTypeProjection E M n i a = 0 :=
  Analysis.HodgeTheory.Decomposition.Projectors.Constructions.spectralProjector_zero _ _ _ i j hij a (pureFormsInDegree_action E M n j a ha)

def manifoldFormFiltration (n : ℕ) (r : ℤ) : Submodule ℂ (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :=
  ⨆ (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n) (_ : r ≤ (i.val.1 : ℤ)), pureFormsInDegree E M n i

theorem manifoldTypeProjection_below (n : ℕ) (r : ℤ) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (ha : a ∈ manifoldFormFiltration E M n r) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n) (hi : (i.val.1 : ℤ) < r) :
    manifoldTypeProjection E M n i a = 0 := by
  have hle : manifoldFormFiltration E M n r ≤ LinearMap.ker (manifoldTypeProjection E M n i) := by
    refine iSup_le fun j => iSup_le fun hj => ?_
    intro b hb
    have hij : i ≠ j := by
      intro h
      subst j
      omega
    exact manifoldTypeProjection_other E M n i j hij b hb
  exact hle ha

theorem mem_manifoldFormFiltration_iff_projections [FiniteDimensional ℝ E]
    (n : ℕ) (r : ℤ) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    a ∈ manifoldFormFiltration E M n r ↔
      ∀ i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n, (i.val.1 : ℤ) < r → manifoldTypeProjection E M n i a = 0 := by
  constructor
  · exact manifoldTypeProjection_below E M n r a
  · intro h
    rw [← sum_manifoldTypeProjection E M n a]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : r ≤ (i.val.1 : ℤ)
    · apply Submodule.mem_iSup_of_mem i
      apply Submodule.mem_iSup_of_mem hi
      exact manifoldTypeProjection_pure E M n i a
    · rw [h i (lt_of_not_ge hi)]
      exact Submodule.zero_mem _

omit [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem manifoldFormFiltration_antitone (n : ℕ) : Antitone (manifoldFormFiltration E M n) := by
  intro r s hrs
  refine iSup_le fun i => iSup_le fun hsi => ?_
  exact le_iSup_of_le i (le_iSup_of_le (hrs.trans hsi) le_rfl)

theorem manifoldFormFiltration_eq_top [FiniteDimensional ℝ E]
    (n : ℕ) (r : ℤ) (hr : r ≤ 0) : manifoldFormFiltration E M n r = ⊤ := by
  apply top_unique
  intro a _
  rw [mem_manifoldFormFiltration_iff_projections]
  intro i hi
  have hn : (0 : ℤ) ≤ i.val.1 := Nat.cast_nonneg _
  omega

omit [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem manifoldFormFiltration_eq_bot (n : ℕ) (r : ℤ) (hr : (n : ℤ) < r) :
    manifoldFormFiltration E M n r = ⊥ := by
  apply le_antisymm
  · refine iSup_le fun i => iSup_le fun hi => ?_
    have := i.property
    omega
  · exact bot_le

end

end OAI.AlgebraicGeometry.Comparison.Betti.ManifoldFormFiltration.Hodge
