import OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.FieldPointLift
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SchemeStalkPullback

/-! # Point Range -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.PointRange

noncomputable section

/-! The complex-point image of a closed immersion is exactly the inverse image of its scheme-point image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem closedImmersion_point_mem_range_iff
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) [IsClosedImmersion f.left]
    (q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) :
    q ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) ↔
      Analytification.Base.analytificationMap Y q ∈ Set.range f.left := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨Analytification.Base.analytificationMap X p, rfl⟩
  · rintro ⟨x, hx⟩
    have hpoint : (IsLocalRing.closedPoint ℂ : Foundations.Scheme.ProjectiveSpace.complexBase) = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.basePoint :=
      Subsingleton.elim _ _
    have hx' : f.left x = q.left (IsLocalRing.closedPoint ℂ) := by
      rw [hpoint]
      exact hx
    obtain ⟨l, hl⟩ := FieldPointLift.closedImmersion_fieldPoint_lift f.left ℂ q.left x hx'
    have hw : l ≫ X.hom = 𝟙 Foundations.Scheme.ProjectiveSpace.complexBase := by
      rw [← Over.w f, ← Category.assoc, hl]
      exact Over.w q
    let p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X := Over.homMk l hw
    refine ⟨p, ?_⟩
    apply Over.OverMorphism.ext
    exact hl

end

end OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.PointRange
