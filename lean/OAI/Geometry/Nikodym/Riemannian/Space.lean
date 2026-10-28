import OAI.Geometry.Nikodym.Riemannian.Distance

noncomputable section
open Set Bundle Manifold
open scoped ContDiff

namespace OAI.Geometry.Nikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A coordinate domain with its intrinsic Riemannian distance. The type
synonym prevents the ambient Euclidean subtype distance from being chosen
instead of the metric supplied by the coefficient field. -/
def IntrinsicDomain (g : SmoothCoordinateMetric E) : Type _ := g.openDomain

namespace IntrinsicDomain

variable (g : SmoothCoordinateMetric E)

instance : TopologicalSpace (IntrinsicDomain g) :=
  inferInstanceAs (TopologicalSpace g.openDomain)

instance : ChartedSpace E (IntrinsicDomain g) :=
  inferInstanceAs (ChartedSpace E g.openDomain)

instance : IsManifold 𝓘(ℝ,E) ∞ (IntrinsicDomain g) :=
  inferInstanceAs (IsManifold 𝓘(ℝ,E) ∞ g.openDomain)

instance : RiemannianBundle (fun x : IntrinsicDomain g => TangentSpace 𝓘(ℝ,E) x) :=
  g.toRiemannianBundle

instance : IsContinuousRiemannianBundle E
    (fun x : IntrinsicDomain g => TangentSpace 𝓘(ℝ,E) x) :=
  g.isContinuousRiemannianBundle

instance : IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E
    (fun x : IntrinsicDomain g => TangentSpace 𝓘(ℝ,E) x) :=
  g.isContMDiffRiemannianBundle

instance : EMetricSpace (IntrinsicDomain g) := g.intrinsicEMetricSpace

instance : IsRiemannianManifold 𝓘(ℝ,E) (IntrinsicDomain g) :=
  g.intrinsic_isRiemannianManifold

def coordinate (x : IntrinsicDomain g) : E := (show g.openDomain from x).val

@[simp] theorem edist_eq (x y : IntrinsicDomain g) :
    edist x y = riemannianEDist 𝓘(ℝ,E) x y :=
  IsRiemannianManifold.out x y

theorem norm_tangent (x : IntrinsicDomain g) (v : TangentSpace 𝓘(ℝ,E) x) :
    ‖v‖ = Real.sqrt (g.inner (IntrinsicDomain.coordinate g x) v v) :=
  g.norm_tangent x v

end IntrinsicDomain
end OAI.Geometry.Nikodym
