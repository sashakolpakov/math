import OAI.AlgebraicTopology.Cohomology.Singular.ConvexResolution
import OAI.AlgebraicTopology.DeRham.Comparison.CechComplexAugmentation

/-! # Euclidean Open Cover -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.EuclideanOpenCover

noncomputable section

/-!
# A convex-ball cover of an actual Euclidean open domain

Each point of the domain is assigned a positive-radius ball contained in the
domain. These balls form an open cover, and all ordered finite intersections
are convex, including empty intersections. No nonemptiness of the domain is
required.
-/

open _root_.TopologicalSpace

variable {E : Type} [NormedAddCommGroup E]

/-- A positive radius whose ball around the given point stays in the open domain. -/
def euclideanOpenBallRadius (W : Opens E) (x : W) : ℝ :=
  Classical.choose (Metric.isOpen_iff.mp W.isOpen x x.property)

theorem euclideanOpenBallRadius_pos (W : Opens E) (x : W) :
    0 < euclideanOpenBallRadius W x :=
  (Classical.choose_spec (Metric.isOpen_iff.mp W.isOpen x x.property)).1

theorem euclideanOpenBallRadius_subset (W : Opens E) (x : W) :
    Metric.ball (x : E) (euclideanOpenBallRadius W x) ⊆ W :=
  (Classical.choose_spec (Metric.isOpen_iff.mp W.isOpen x x.property)).2

/-- The cover consists of actual balls centered at points of the domain. -/
def euclideanOpenBallCover (W : Opens E) (x : W) : Opens E :=
  ⟨Metric.ball (x : E) (euclideanOpenBallRadius W x), Metric.isOpen_ball⟩

theorem euclideanOpenBallCover_le (W : Opens E) (x : W) :
    euclideanOpenBallCover W x ≤ W :=
  euclideanOpenBallRadius_subset W x

theorem euclideanOpenBallCover_center (W : Opens E) (x : W) :
    (x : E) ∈ euclideanOpenBallCover W x :=
  Metric.mem_ball_self (euclideanOpenBallRadius_pos W x)

/-- The balls cover every point of the domain, also when the domain is empty. -/
theorem euclideanOpenBallCover_covers (W : Opens E) (x : W) :
    ∃ i : W, (x : E) ∈ euclideanOpenBallCover W i :=
  ⟨x, euclideanOpenBallCover_center W x⟩

variable [NormedSpace ℝ E]

theorem euclideanOpenBallCover_convex (W : Opens E) (x : W) :
    Convex ℝ (euclideanOpenBallCover W x : Set E) :=
  convex_ball (x : E) (euclideanOpenBallRadius W x)

/-- Every ordered intersection used by the Čech construction is convex. -/
theorem euclideanOpenBallCover_intersection_convex (W : Opens E)
    {p : ℕ} (a : Fin (p + 1) → W) :
    Convex ℝ (SmoothCech.cechIntersection (euclideanOpenBallCover W) a : Set E) :=
  Cohomology.Singular.ConvexResolution.convex_cechIntersection (euclideanOpenBallCover W)
    (euclideanOpenBallCover_convex W) a

end

end OAI.AlgebraicTopology.DeRham.Comparison.EuclideanOpenCover
