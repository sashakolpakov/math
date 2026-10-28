import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormFiniteness
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules

/-! # Form Coherence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.FormCoherence.Integral

noncomputable section

/-! All-degree coherence of the original differential-form module sheaf
on a smooth proper scheme over an arbitrary commutative base ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  [IsProper X.hom] [Smooth X.hom]

theorem quasicoherent (n : ℕ) :
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n).IsQuasicoherent :=
  AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormFiniteness.BaseSmoothProperOrdinaryFormFiniteness.quasicoherent R X n

theorem finiteType (n : ℕ) :
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n).IsFiniteType :=
  AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormFiniteness.BaseSmoothProperOrdinaryFormFiniteness.finiteType R X n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.FormCoherence.Integral
