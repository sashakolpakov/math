import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularSet
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! # Small Simplex -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSimplex.Cycles

noncomputable section

/-!
# The geometric smallness step for singular excision

Pulling an open cover back along an actual singular simplex gives a Lebesgue
number on its compact standard-simplex domain. Consequently all sufficiently
small continuous subsimplices are subordinate to the cover. A single scale,
and then a single geometric-shrinking exponent, works for any finite family
of singular simplices.

This file does not assume or construct a subdivision chain operator. Its final
theorem supplies the geometric conclusion once a concrete subsimplex map has
the stated diameter bound. Constructing the barycentric chain operator and its
chain homotopy remains a separate obligation.
-/

open _root_.CategoryTheory
open scoped Simplicial

variable {X : TopCat.{0}} {ι : Type} (U : ι → Set X)
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)

include hopen hcover

/-- Every singular simplex has a positive scale at which balls in its domain
map into single cover members. This is the actual pulled-back-cover Lebesgue
number, not an assumption on a prospective chain map. -/
theorem singularSimplex_lebesgueNumber {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)) :
    ∃ ε > 0, ∀ x : Convexity.StdSimplex ℝ (Fin (n + 1)),
      ∃ i, Metric.ball x ε ⊆ σ ⁻¹' U i := by
  have hpull : ∀ i, IsOpen (σ ⁻¹' U i) :=
    fun i ↦ (hopen i).preimage σ.continuous
  have hpullcover : (Set.univ : Set (Convexity.StdSimplex ℝ (Fin (n + 1)))) ⊆
      ⋃ i, σ ⁻¹' U i := by
    intro x _
    obtain ⟨i, hi⟩ := hcover (σ x)
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨ε, hε, hsmall⟩ :=
    lebesgue_number_lemma_of_metric isCompact_univ hpull hpullcover
  exact ⟨ε, hε, fun x ↦ hsmall x (Set.mem_univ x)⟩

/-- Small diameter of an actual continuous subsimplex implies that its
composition with the original singular simplex lies in one cover member. -/
theorem singularSimplex_small_subsimplices {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)) :
    ∃ ε > 0, ∀ (m : ℕ) (τ : C(Convexity.StdSimplex ℝ (Fin (m + 1)),
      Convexity.StdSimplex ℝ (Fin (n + 1)))),
      (∀ a b, dist (τ a) (τ b) < ε) →
      ∃ i, Set.range (σ.comp τ) ⊆ U i := by
  obtain ⟨ε, hε, hball⟩ := singularSimplex_lebesgueNumber U hopen hcover σ
  refine ⟨ε, hε, ?_⟩
  intro m τ hτ
  let a : Convexity.StdSimplex ℝ (Fin (m + 1)) := Convexity.StdSimplex.single 0
  obtain ⟨i, hi⟩ := hball (τ a)
  refine ⟨i, ?_⟩
  rintro _ ⟨b, rfl⟩
  exact hi (hτ b a)

/-- A finite family of genuine singular simplices admits one common
smallness scale. This is the finite-support step needed for singular chains. -/
theorem singularSimplices_uniform_smallness {n : ℕ}
    (s : Finset C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)) :
    ∃ ε > 0, ∀ σ ∈ s, ∀ (m : ℕ)
      (τ : C(Convexity.StdSimplex ℝ (Fin (m + 1)), Convexity.StdSimplex ℝ (Fin (n + 1)))),
      (∀ a b, dist (τ a) (τ b) < ε) →
      ∃ i, Set.range (σ.comp τ) ⊆ U i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, zero_lt_one, ?_⟩
      intro σ hσ
      exact (Finset.notMem_empty σ hσ).elim
  | @insert σ s _ ih =>
      obtain ⟨δ, hδ, hσ⟩ := singularSimplex_small_subsimplices U hopen hcover σ
      obtain ⟨ε, hε, hs⟩ := ih
      refine ⟨min δ ε, lt_min hδ hε, ?_⟩
      intro ψ hψ m τ hτ
      rcases Finset.mem_insert.mp hψ with rfl | hψ
      · exact hσ m τ (fun a b ↦ (hτ a b).trans_le (min_le_left δ ε))
      · exact hs ψ hψ m τ (fun a b ↦ (hτ a b).trans_le (min_le_right δ ε))

/-- Geometric mesh contraction eventually makes every subsimplex in a finite
family subordinate to an open cover. The diameter hypothesis is explicit;
no subdivision identity or mesh estimate is smuggled in as structure data. -/
theorem singularSimplices_geometric_smallness {n : ℕ}
    (s : Finset C(Convexity.StdSimplex ℝ (Fin (n + 1)), X))
    {r : ℝ} (hr : r < 1) :
    ∃ N : ℕ, ∀ σ ∈ s, ∀ (m : ℕ)
      (τ : C(Convexity.StdSimplex ℝ (Fin (m + 1)), Convexity.StdSimplex ℝ (Fin (n + 1)))),
      (∀ a b, dist (τ a) (τ b) ≤ r ^ N) →
      ∃ i, Set.range (σ.comp τ) ⊆ U i := by
  obtain ⟨ε, hε, hsmall⟩ := singularSimplices_uniform_smallness U hopen hcover s
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hr
  refine ⟨N, ?_⟩
  intro σ hσ m τ hτ
  exact hsmall σ hσ m τ (fun a b ↦ (hτ a b).trans_lt hN)

omit hopen hcover in
/-- The geometric containment result packages into the actual small singular
simplex type used by the cover Čech resolution. -/
def smallSingularSimplexOfRange {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X))
    (hσ : ∃ i, Set.range σ ⊆ U i) :
    AlgebraicTopology.DeRham.Comparison.CechCoverRows.SmallSingularSimplex X U n :=
  ⟨(X.toSSetObjEquiv (.op ⦋n⦌)).symm σ, by
    simpa only [Equiv.apply_symm_apply] using hσ⟩

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSimplex.Cycles
