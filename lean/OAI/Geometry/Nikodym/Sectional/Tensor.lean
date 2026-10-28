import OAI.Geometry.Nikodym.Sectional.Symmetry
import OAI.Geometry.Nikodym.Sectional.MetricAlgebra
import OAI.Geometry.Nikodym.Sectional.Polarization

noncomputable section
namespace OAI.Geometry.Nikodym.SmoothCoordinateMetric

open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (g : SmoothCoordinateMetric E)

/-- The full tensor identity follows from the scalar unnormalized
sectional identities for the actual constructed curvature. -/
theorem curvature_eq_of_sectional_identity {κ : ℝ} {x : E} (hx : x ∈ g.domain)
    (hsection : ∀ u v, g.inner x (g.curvature x u v v) u =
      κ * (g.inner x u u * g.inner x v v - g.inner x u v ^ 2)) (u v w : E) :
    g.curvature x u v w = κ • (g.inner x v w • u - g.inner x u w • v) := by
  let T : E → E → E → E → ℝ := fun a b c d =>
    g.inner x (g.curvature x a b c) d -
      κ * (g.inner x b c * g.inner x a d - g.inner x a c * g.inner x b d)
  have hT : ∀ a b c d, T a b c d = 0 := by
    apply curvature_tensor_zero_of_sectional_zero T
    · intro a b c d e
      simp only [T,g.curvature_add_first hx,g.inner_add_first]
      ring
    · intro a b c d e
      simp only [T,g.curvature_add_second hx,g.inner_add_first]
      ring
    · intro a b c d e
      simp only [T,g.curvature_add_third hx,g.inner_add_first,g.inner_add_second]
      ring
    · intro a b c d e
      simp only [T,g.inner_add_second]
      ring
    · intro a b c d
      dsimp only [T]
      rw [g.curvature_swap,g.inner_neg_first]
      ring
    · intro a b c d
      dsimp only [T]
      rw [g.curvature_inner_swap_last hx]
      ring
    · intro a b c d
      have he := congrArg (fun q => g.inner x q d) (g.curvature_bianchi hx a b c)
      simp only [g.inner_add_first,g.inner_zero_first] at he
      dsimp only [T]
      rw [g.inner_symmetric hx c b,g.inner_symmetric hx c a,g.inner_symmetric hx b a]
      linear_combination he
    · intro a b
      dsimp only [T]
      rw [hsection,g.inner_symmetric hx b a]
      ring
  let d := g.curvature x u v w - κ • (g.inner x v w • u - g.inner x u w • v)
  have hz : g.inner x d d = 0 := by
    have he := hT u v w d
    simpa only [T,d,g.inner_sub_first,g.inner_smul_first,mul_sub] using he
  have hd : d = 0 := by
    by_contra hn
    exact (g.positive x hx d hn).ne' hz
  exact sub_eq_zero.mp hd

end OAI.Geometry.Nikodym.SmoothCoordinateMetric
