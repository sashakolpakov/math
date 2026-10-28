import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.SectionCotangent
import Mathlib.Algebra.Module.FinitePresentation

/-! # Conormal Finite -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Section.ConormalFinite.BundleCycles

noncomputable section

/-! # LineBundleCycles: finite projective conormal modules from actual smooth finite-type sections -/

open KaehlerDifferential TensorProduct

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra B A]
    [IsScalarTower A B A] [Algebra.FormallySmooth A B] [Algebra.EssFiniteType A B]

theorem sectionConormal_finite : Module.Finite A (RingHom.ker (algebraMap B A)).Cotangent := by
  have : Module.Finite A (A ⊗[B] Ω[B⁄A]) := inferInstance
  exact Module.Finite.equiv (Smooth.SectionCotangent.BundleCycles.smoothSectionCotangentEquiv A B).symm

theorem sectionConormal_finitePresentation :
    Module.FinitePresentation A (RingHom.ker (algebraMap B A)).Cotangent := by
  have := sectionConormal_finite A B
  exact Module.finitePresentation_of_projective A _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Section.ConormalFinite.BundleCycles
