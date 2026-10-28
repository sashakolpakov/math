import OAI.Geometry.Nikodym.Sectional.Tensor

noncomputable section
namespace OAI.Geometry.Nikodym.SmoothCoordinateMetric

open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (g : SmoothCoordinateMetric E)

def sectionalDenominator (x u v : E) : ℝ :=
  g.inner x u u * g.inner x v v - g.inner x u v ^ 2

/-- Scalar sectional curvature of the plane spanned by `u,v`. The usual
geometric interpretation applies when the Gram denominator is nonzero. -/
def sectionalCurvature (x u v : E) : ℝ :=
  g.inner x (g.curvature x u v v) u / g.sectionalDenominator x u v

/-- The scalar constant-sectional-curvature condition, imposed only on
nondegenerate tangent planes. No tensor identity is built into it. -/
def HasConstantSectionalCurvature (κ : ℝ) : Prop :=
  ∀ x ∈ g.domain, ∀ u v, g.sectionalDenominator x u v ≠ 0 →
    g.sectionalCurvature x u v = κ

theorem sectional_numerator_zero_of_degenerate {x : E} (hx : x ∈ g.domain)
    (u v : E) (hdeg : g.sectionalDenominator x u v = 0) :
    g.inner x (g.curvature x u v v) u = 0 := by
  by_cases hu : u = 0
  · subst u
    exact g.inner_zero_second x _
  have huu : 0 < g.inner x u u := g.positive x hx u hu
  have huv : g.inner x v u = g.inner x u v := g.inner_symmetric hx v u
  let a : ℝ := g.inner x u v / g.inner x u u
  have hw : g.inner x (v-a•u) (v-a•u) = 0 := by
    simp only [g.inner_sub_first,g.inner_sub_second,
      g.inner_smul_first,g.inner_smul_second,huv]
    dsimp only [a]
    dsimp only [SmoothCoordinateMetric.sectionalDenominator] at hdeg
    field_simp [huu.ne']
    nlinarith
  have hw0 : v-a•u = 0 := by
    by_contra hn
    exact (g.positive x hx (v-a•u) hn).ne' hw
  have hv : v = a•u := sub_eq_zero.mp hw0
  rw [hv,g.curvature_smul_second hx,g.curvature_self,smul_zero,g.inner_zero_first]

theorem HasConstantSectionalCurvature.tensor_identity {κ : ℝ}
    (hκ : g.HasConstantSectionalCurvature κ) : g.HasConstantCurvature κ := by
  intro x hx u v w
  apply g.curvature_eq_of_sectional_identity hx
  intro a b
  by_cases hdeg : g.sectionalDenominator x a b = 0
  · rw [g.sectional_numerator_zero_of_degenerate hx a b hdeg]
    change 0 = κ * g.sectionalDenominator x a b
    rw [hdeg,mul_zero]
  · have hh := hκ x hx a b hdeg
    exact (div_eq_iff hdeg).mp hh

theorem HasConstantCurvature.sectional_identity {κ : ℝ}
    (hκ : g.HasConstantCurvature κ) : g.HasConstantSectionalCurvature κ := by
  intro x hx u v hdeg
  dsimp only [SmoothCoordinateMetric.sectionalCurvature]
  rw [hκ x hx u v v,g.inner_smul_first,g.inner_sub_first,
    g.inner_smul_first,g.inner_smul_first,g.inner_symmetric hx v u]
  apply (div_eq_iff hdeg).mpr
  dsimp only [SmoothCoordinateMetric.sectionalDenominator]
  ring

theorem constant_sectional_iff_tensor (κ : ℝ) :
    g.HasConstantSectionalCurvature κ ↔ g.HasConstantCurvature κ :=
  ⟨fun h => h.tensor_identity g,fun h => h.sectional_identity g⟩

end OAI.Geometry.Nikodym.SmoothCoordinateMetric
