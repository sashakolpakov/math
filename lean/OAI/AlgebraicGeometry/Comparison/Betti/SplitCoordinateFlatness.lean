import OAI.AlgebraicGeometry.Comparison.Betti.SplitCoordinateCompletion
import OAI.AlgebraicGeometry.Comparison.Betti.FaithfulLocalCompletion
import OAI.AlgebraicGeometry.Comparison.Betti.FlatDescentTower
import Mathlib.RingTheory.Polynomial.Basic

/-! # Split Coordinate Flatness -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SplitCoordinateFlatness.AnalyticLocal

noncomputable section

/-! A split regular coordinate in a Noetherian local ring gives a flat
map from the coefficient polynomial ring, by completion and descent. -/

open _root_.Polynomial

theorem split_coordinate_flatness {A B : Type*} [CommRing A] [CommRing B] [IsDomain B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing B] [Algebra A[X] B]
    (s : A →+* B) (r : B →+* A) (hrs : r.comp s = RingHom.id A)
    (t : B) (hrt : r t = 0) (ht : t ≠ 0) (htm : t ∈ IsLocalRing.maximalIdeal B)
    (hdivision : ∀ y : B, ∃ b : B, y = s (r y) + t * b)
    (hAlg : algebraMap A[X] B = eval₂RingHom s t) : Module.Flat A[X] B := by
  let J : Ideal B := Ideal.span {t}
  have hJ : J ≤ IsLocalRing.maximalIdeal B :=
    (Ideal.span_singleton_le_iff_mem _).mpr htm
  let : Module.FaithfullyFlat B (AdicCompletion J B) := FaithfulLocalCompletion.Analytic.local_completion_faithfullyFlat B J hJ
  let e := SplitCoordinateCompletion.AnalyticLocal.splitCoordinateCompletionAlgEquiv s r hrs t hrt ht hdivision hAlg
  let : Module.Flat A[X] (AdicCompletion J B) := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  exact FlatDescentTower.AnalyticLocal.flat_of_faithfullyFlat_extension A[X] B (AdicCompletion J B)

end

end OAI.AlgebraicGeometry.Comparison.Betti.SplitCoordinateFlatness.AnalyticLocal
