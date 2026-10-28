import OAI.Geometry.Nikodym.Riemannian.Space
import OAI.Geometry.Nikodym.Riemannian.Lower
import OAI.Geometry.Nikodym.Riemannian.Convex

noncomputable section
open Set Bundle Manifold
open scoped ContDiff ENNReal

namespace OAI.Geometry.Nikodym.IntrinsicDomain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (g : SmoothCoordinateMetric E)

def ofCoordinate (x : g.openDomain) : IntrinsicDomain g := x

omit [FiniteDimensional ℝ E] in
@[simp] theorem coordinate_ofCoordinate (x : g.openDomain) :
    IntrinsicDomain.coordinate g (IntrinsicDomain.ofCoordinate g x) = (x : E) := rfl

omit [FiniteDimensional ℝ E] in
theorem coordinate_mem (x : IntrinsicDomain g) : IntrinsicDomain.coordinate g x ∈ g.domain :=
  (show g.openDomain from x).property

omit [FiniteDimensional ℝ E] in
theorem coordinate_injective : Function.Injective (IntrinsicDomain.coordinate g) := by
  intro x y h
  exact Subtype.ext h

omit [FiniteDimensional ℝ E] in
theorem contMDiff_coordinate :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (IntrinsicDomain.coordinate g) :=
  contMDiff_subtype_val

/-- Lower ellipticity gives the Lipschitz bound from intrinsic geometry
to Euclidean coordinates. -/
theorem lipschitz_coordinate {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x ∈ g.domain, ∀ v, c * ‖v‖^2 ≤ g.inner x v v) :
    LipschitzWith ⟨1 / Real.sqrt c,by positivity⟩ (IntrinsicDomain.coordinate g) := by
  intro x y
  rw [IntrinsicDomain.edist_eq]
  have h := g.edist_coordinate_le_riemannianEDist hc hcoer x y
  rw [ENNReal.ofReal_eq_coe_nnreal (show 0 ≤ 1 / Real.sqrt c by positivity)] at h
  exact h

/-- On a convex coordinate domain, upper ellipticity supplies the
inverse Lipschitz bound using actual straight paths. -/
theorem lipschitz_ofCoordinate (hconv : Convex ℝ g.domain)
    {C : ℝ} (hC : 0 < C)
    (hupper : ∀ x ∈ g.domain, ∀ v, g.inner x v v ≤ C * ‖v‖^2) :
    LipschitzWith ⟨Real.sqrt C,Real.sqrt_nonneg _⟩ (IntrinsicDomain.ofCoordinate g) := by
  intro x y
  rw [IntrinsicDomain.edist_eq]
  have h := g.riemannianEDist_le_of_convex hconv hC hupper x y
  rw [ENNReal.ofReal_eq_coe_nnreal (Real.sqrt_nonneg C)] at h
  exact h

end OAI.Geometry.Nikodym.IntrinsicDomain
