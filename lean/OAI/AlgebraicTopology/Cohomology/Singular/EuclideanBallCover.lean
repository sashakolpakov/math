import OAI.AlgebraicTopology.Cohomology.Singular.ChartOpenDiffeomorph
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech
import Mathlib.Analysis.Normed.Module.Convex

/-! # Euclidean Ball Cover -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.EuclideanBallCover

noncomputable section

/-!
# An explicit convex-intersection ball cover of an open normed-space domain

Openness provides a positive radius at every point of the domain. The actual
preimages of these ambient balls cover the open subspace. Every ordered
Čech intersection, including an empty intersection set, flattens to exactly
the corresponding intersection of ambient balls and hence is convex there.
-/

open _root_.TopologicalSpace
open OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech
open scoped _root_.Manifold ContDiff

universe u

variable {E : Type u} [NormedAddCommGroup E] (U : Opens E)

/-- A positive radius whose ambient ball remains in the given open set. -/
def euclideanBallRadius (x : U) : ℝ :=
  (Metric.isOpen_iff.mp U.isOpen (x : E) x.property).choose

theorem euclideanBallRadius_pos (x : U) : 0 < euclideanBallRadius U x :=
  (Metric.isOpen_iff.mp U.isOpen (x : E) x.property).choose_spec.1

theorem euclideanBallRadius_ball_subset (x : U) :
    Metric.ball (x : E) (euclideanBallRadius U x) ⊆ (U : Set E) :=
  (Metric.isOpen_iff.mp U.isOpen (x : E) x.property).choose_spec.2

/-- The chosen ball as an actual ambient open subset. -/
def euclideanAmbientBall (x : U) : Opens E :=
  ⟨Metric.ball (x : E) (euclideanBallRadius U x), Metric.isOpen_ball⟩

theorem euclideanAmbientBall_le (x : U) : euclideanAmbientBall U x ≤ U :=
  euclideanBallRadius_ball_subset U x

theorem convex_euclideanAmbientBall [NormedSpace ℝ E] (x : U) :
    Convex ℝ (euclideanAmbientBall U x : Set E) :=
  convex_ball (x : E) (euclideanBallRadius U x)

/-- The cover member is literally the inverse image of the ambient ball
under the open-subspace inclusion. -/
def euclideanBallCover (x : U) : Opens U :=
  ⟨Subtype.val ⁻¹' (euclideanAmbientBall U x : Set E),
    (euclideanAmbientBall U x).isOpen.preimage continuous_subtype_val⟩

@[simp]
theorem mem_euclideanBallCover (x y : U) :
    y ∈ euclideanBallCover U x ↔ (y : E) ∈ euclideanAmbientBall U x := Iff.rfl

theorem euclideanBallCover_mem_self (x : U) : x ∈ euclideanBallCover U x :=
  Metric.mem_ball_self (euclideanBallRadius_pos U x)

/-- The chosen ambient balls cover precisely the original open set. -/
theorem euclideanAmbientBall_iSup : (⨆ x : U, euclideanAmbientBall U x) = U := by
  apply le_antisymm
  · exact iSup_le (euclideanAmbientBall_le U)
  · intro y hy
    change y ∈ ((⨆ x : U, euclideanAmbientBall U x : Opens E) : Set E)
    rw [Opens.coe_iSup]
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self (euclideanBallRadius_pos U ⟨y, hy⟩)⟩

/-- The inverse-image balls are an actual open cover of the subspace. -/
theorem euclideanBallCover_iSup : (⨆ x : U, euclideanBallCover U x) = ⊤ := by
  apply top_unique
  intro y _
  change y ∈ ((⨆ x : U, euclideanBallCover U x : Opens U) : Set U)
  rw [Opens.coe_iSup]
  exact Set.mem_iUnion.mpr ⟨y, euclideanBallCover_mem_self U y⟩

/-- Forgetting the subspace layer of a cover member gives exactly its
chosen ambient ball. -/
theorem nestedOpenImage_euclideanBallCover (x : U) :
    ChartOpenDiffeomorph.nestedOpenImage U (euclideanBallCover U x) = euclideanAmbientBall U x := by
  apply Opens.ext
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro hy
    exact ⟨⟨y, euclideanAmbientBall_le U x hy⟩, hy, rfl⟩

/-- A nonempty ordered tuple of ambient balls has its intersection inside
the original open set, even when the intersection set itself is empty. -/
theorem euclideanAmbientBall_cech_le {p : ℕ} (a : Fin (p + 1) → U) :
    DeRham.Comparison.SmoothCech.cechIntersection (euclideanAmbientBall U) a ≤ U :=
  (DeRham.Comparison.SmoothCech.cechIntersection_le (euclideanAmbientBall U) a 0).trans
    (euclideanAmbientBall_le U (a 0))

/-- Every ordered Čech intersection in the cover flattens to precisely the
corresponding intersection of ambient balls. No point of the intersection
is selected and no nonemptiness assumption is required. -/
theorem nestedOpenImage_euclideanBallCover_cech {p : ℕ} (a : Fin (p + 1) → U) :
    ChartOpenDiffeomorph.nestedOpenImage U (DeRham.Comparison.SmoothCech.cechIntersection (euclideanBallCover U) a) =
      DeRham.Comparison.SmoothCech.cechIntersection (euclideanAmbientBall U) a := by
  apply Opens.ext
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    apply (DeRham.Comparison.SmoothCech.mem_cechIntersection (euclideanAmbientBall U) a (z : E)).2
    intro k
    exact (DeRham.Comparison.SmoothCech.mem_cechIntersection (euclideanBallCover U) a z).1 hz k
  · intro hy
    let z : U := ⟨y, euclideanAmbientBall_cech_le U a hy⟩
    refine ⟨z, ?_, rfl⟩
    apply (DeRham.Comparison.SmoothCech.mem_cechIntersection (euclideanBallCover U) a z).2
    intro k
    exact (DeRham.Comparison.SmoothCech.mem_cechIntersection (euclideanAmbientBall U) a y).1 hy k

variable [NormedSpace ℝ E]

/-- Every ambient intersection of the chosen balls is convex. -/
theorem convex_euclideanAmbientBall_cech {p : ℕ} (a : Fin (p + 1) → U) :
    Convex ℝ (DeRham.Comparison.SmoothCech.cechIntersection (euclideanAmbientBall U) a : Set E) := by
  change Convex ℝ ((⨅ k, euclideanAmbientBall U (a k) : Opens E) : Set E)
  rw [Opens.coe_iInf]
  exact convex_iInter (fun k => convex_euclideanAmbientBall U (a k))

/-- Every cover Čech intersection has a convex actual ambient open image. -/
theorem convex_nestedOpenImage_euclideanBallCover_cech {p : ℕ} (a : Fin (p + 1) → U) :
    Convex ℝ (ChartOpenDiffeomorph.nestedOpenImage U (DeRham.Comparison.SmoothCech.cechIntersection (euclideanBallCover U) a) : Set E) := by
  rw [nestedOpenImage_euclideanBallCover_cech]
  exact convex_euclideanAmbientBall_cech U a

/-- The actual Čech intersection is smoothly identified with its convex
ambient open image by flattening the nested open-subspace structure. -/
def euclideanBallCoverCechDiffeomorph {p : ℕ} (a : Fin (p + 1) → U) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (DeRham.Comparison.SmoothCech.cechIntersection (euclideanBallCover U) a)
      (ChartOpenDiffeomorph.nestedOpenImage U (DeRham.Comparison.SmoothCech.cechIntersection (euclideanBallCover U) a)) ∞ :=
  ChartOpenDiffeomorph.nestedOpenDiffeomorph E U (DeRham.Comparison.SmoothCech.cechIntersection (euclideanBallCover U) a)

@[simp]
theorem euclideanBallCoverCechDiffeomorph_apply {p : ℕ} (a : Fin (p + 1) → U)
    (y : DeRham.Comparison.SmoothCech.cechIntersection (euclideanBallCover U) a) :
    (euclideanBallCoverCechDiffeomorph U a y : E) = ((y : U) : E) := rfl

end

end OAI.AlgebraicTopology.Cohomology.Singular.EuclideanBallCover
