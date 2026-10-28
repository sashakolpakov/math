import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineCharts
import OAI.AlgebraicGeometry.Foundations.Scheme.PresentationDimension
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-! # Analytic Isolated Dimension -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.AnalyticIsolatedDimension.Abelian

noncomputable section

/-!
An analytically isolated point of a standard-smooth complex algebra forces
its actual chart dimension to be zero. The algebra is therefore étale over
the complex field and Artinian, so its scheme spectrum is discrete.
-/

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineCharts
open scoped Classical _root_.Topology

variable {A I J : Type} [CommRing A] [Algebra ℂ A] [Fintype I] [Fintype J]

theorem standardSmooth_artinian_of_analytic_isolated
    (P : Algebra.SubmersivePresentation ℂ A I J) (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)
    (hx : IsOpen ({x} : Set (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A))) : IsArtinianRing A := by
  obtain ⟨e, hex, _, _⟩ := AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineCharts.exists_standardSmooth_point_chart P x
  have himage : IsOpen ({e x} : Set (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ)) := by
    simpa only [Set.image_singleton] using
      e.isOpen_image_of_subset_source hx (Set.singleton_subset_iff.mpr hex)
  have hcard : Fintype.card (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map) = 0 := by
    by_contra h
    let : Nonempty (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map) := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero h)
    let : PerfectSpace (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ) := perfectSpace_of_module ℂ _
    exact not_isOpen_singleton (e x) himage
  have hdim : P.dimension = 0 :=
    (AlgebraicGeometry.Foundations.Scheme.PresentationDimension.Algebraic.card_free_variables_eq_dimension P.toPreSubmersivePresentation).symm.trans hcard
  let : Algebra.IsStandardSmoothOfRelativeDimension 0 ℂ A :=
    P.isStandardSmoothOfRelativeDimension hdim
  let : Algebra.Etale ℂ A := inferInstance
  let : Module.Finite ℂ A := Algebra.FormallyUnramified.finite_of_free ℂ A
  exact IsArtinianRing.of_finite ℂ A

end

end OAI.ArithmeticGeometry.Descent.CMVariety.AnalyticIsolatedDimension.Abelian
