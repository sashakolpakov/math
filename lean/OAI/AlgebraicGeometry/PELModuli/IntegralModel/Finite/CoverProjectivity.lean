import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.FiberProjectiveClassifier
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.TestHilbertPolynomial

/-! # Cover Projectivity -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.CoverProjectivity

noncomputable section

/-! Projectivity descends through a finite faithfully flat cover onto
a proper integral scheme. The actual fiber polynomial and its projective
Hilbert classifier are constructed, rather than assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem integral_target_projective_of_finite_flat_cover
    {S : Scheme.{0}} [IsLocallyNoetherian S] {X Y : Over S}
    (q : X ⟶ Y) [IsFinite q.left] [Flat q.left] [Surjective q.left]
    [LocallyOfFinitePresentation q.left] [IsProper Y.hom] [IsIntegral Y.left]
    (BX : HilbertScheme.Presentations.Has.Core.ProjectivePresentation X) : HilbertScheme.Presentations.Has.Core.IsProjectiveOver Y := by
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  obtain ⟨P, hP⟩ := Integral.TestHilbertPolynomial.exists_integral_test_fiber_polynomial BX (FiberHilbertFamily.finiteFiberHilbertFamily q)
  exact FiberProjectiveClassifier.finite_cover_target_projective_of_fiber_polynomial q BX P hP

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.CoverProjectivity
