import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter
import OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry

/-! # Abelian Projective Presentation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AbelianProjectivePresentation.CM

noncomputable section

/-! Construct the literal projective presentation required by GeometricComparison
on the actual complex fiber of its abelian model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]}
  (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq) (j : K →+* ℂ)

def presentation : Foundations.Scheme.SmoothProjective.ProjectivePresentation
    (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom :=
  AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.nativeProjectivePresentation
    (Classical.choice (GroupProjectivity.CM.projective (A.complexFiber j).scheme))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AbelianProjectivePresentation.CM
