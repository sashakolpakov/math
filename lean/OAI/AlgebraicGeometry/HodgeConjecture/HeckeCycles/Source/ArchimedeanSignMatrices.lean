import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanForms
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PolarizationSigns
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.OppositeCoordinates

/-! # Archimedean Sign Matrices -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanSignMatrices.CM

noncomputable section

/-! The source's normalized archimedean matrices have exactly the ball
signature and prescribed multiplicity signs in the oriented convention. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanForms.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E}

theorem hermitian_sign (v : Fin places.count) (i : Fin 3) :
    (if 0 < ArchimedeanForms.CM.hermitianReal E (B := B) v i then (1 : ℂ) else -1) =
      if v = places.distinguished ∧ i = 2 then -1 else 1 := by
  by_cases hi : i = 2
  · subst i
    change (if 0 < (ReferenceDatum.CM.embeddings E places v B.b).re then (1 : ℂ) else -1) = _
    by_cases hv : v = places.distinguished
    · subst v
      rw [ReferenceDatum.CM.embeddings_distinguished]
      simp only [and_self, ite_true]
      exact ite_eq_right (not_lt_of_ge B.negative.le)
    · have hp := (ReferenceDatum.CM.source_signature E B places).2.2.2 v hv
      simp [hv, hp]
  · simp [ArchimedeanForms.CM.hermitianReal, QuadraticForms.CM.coefficient, hi]

variable {d : Gal(E/ℚ) → Bool} (L : GeometricSource.CM.LinePeriod E B places d)

def positive (v : Fin places.count) : Bool :=
  if v = places.distinguished then false else !(d (places.representative v))

theorem opposite_coefficient (v : Fin places.count) :
    ArchimedeanForms.CM.skewReal E (OppositeCoordinates.CM.coordinates E L.coordinates) v =
      2 * (ReferenceDatum.CM.embeddings E places v (L.coordinates.delta * L.coordinates.a)).im := by
  rw [ArchimedeanForms.CM.skew_trace_coefficient]
  have he : (OppositeCoordinates.CM.coordinates E L.coordinates).delta *
      (OppositeCoordinates.CM.coordinates E L.coordinates).a =
        -(L.coordinates.delta * L.coordinates.a) := by
    change L.coordinates.delta * -L.coordinates.a = _
    ring
  rw [he, map_neg, Complex.neg_im]
  ring

theorem skew_sign (v : Fin places.count) :
    (if 0 < ArchimedeanForms.CM.skewReal E (OppositeCoordinates.CM.coordinates E L.coordinates) v then (1 : ℂ) else -1) *
      Complex.I = if positive E (places := places) (d := d) v then Complex.I else -Complex.I := by
  rw [opposite_coefficient]
  by_cases hv : v = places.distinguished
  · subst v
    rw [ReferenceDatum.CM.embeddings_distinguished]
    change (if 0 < 2 * ((L.coordinates.delta * L.coordinates.a : E) : ℂ).im then (1 : ℂ) else -1) *
      Complex.I = _
    have hn := PolarizationSigns.CM.distinguished_negative E L
    have hnot : ¬ 0 < 2 * ((L.coordinates.delta * L.coordinates.a : E) : ℂ).im := by linarith
    rw [ite_eq_right hnot]
    simp [positive]
  · cases hd : d (places.representative v)
    · have hp : 0 < (ReferenceDatum.CM.embeddings E places v (L.coordinates.delta * L.coordinates.a)).im :=
        PolarizationSigns.CM.compact_positive E L v hv hd
      rw [ite_eq_left (mul_pos (by norm_num : (0 : ℝ) < 2) hp)]
      simp [positive, hv, hd]
    · have hn : (ReferenceDatum.CM.embeddings E places v (L.coordinates.delta * L.coordinates.a)).im < 0 :=
        PolarizationSigns.CM.compact_negative E L v hv hd
      have hnot : ¬ 0 < 2 * (ReferenceDatum.CM.embeddings E places v (L.coordinates.delta * L.coordinates.a)).im := by linarith
      rw [ite_eq_right hnot]
      simp [positive, hv, hd]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanSignMatrices.CM
