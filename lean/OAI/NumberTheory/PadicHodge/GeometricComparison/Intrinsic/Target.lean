import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.NormalizedPoints
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.NormalizedPointCriterion
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.BalancedTopNonvanishing
import OAI.NumberTheory.PadicHodge.GeometricComparison.ZeroDimensional

/-! # Target -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

set_option Elab.async false

/-! The original geometric inputs imply the full comparison target.
Positive dimension uses the native top cup and the normalized point
comparison; dimension zero uses the actual finite-scheme cohomology. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.native_comparisonTarget
    {H : Type} [CommRing H] [Algebra ℚ H]
    (κ : K →+* AlgebraicClosure ℚ) (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (hplace : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = ι.comp κ)
    (ρ : A.HeckeRealization H)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    HeckeScalar.ComparisonTarget q κ jComplex ι jq A H ρ P ℓ := by
  by_cases h0 : A.dimension = 0
  · exact ZeroDimensional.comparison_and_weak_admissibility_of_dimension_zero
      q κ jComplex ι jq hplace A h0 H ρ P ℓ hℓq
  · have hpos : 0 < A.dimension := Nat.pos_of_ne_zero h0
    let : ConnectedSpace A.specialFiber.scheme.left :=
      GeometricallyConnected.connectedSpace_of_subsingleton A.specialFiber.scheme.hom
    let y : A.specialFiber.scheme.left :=
      Classical.choice (inferInstance : Nonempty A.specialFiber.scheme.left)
    exact A.projective_comparisonTarget_of_normalized_points
      κ jComplex ι hplace ρ P ℓ hℓq hpos y
      (A.nativeBalancedTopCup_nonzero (jComplex.comp κ) P hpos)
      (fun n m hm => A.truncatedNormalizedPointEquality n m hm hpos)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
