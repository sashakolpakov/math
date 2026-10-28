import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexPairing
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RealStructure
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SiegelGraphPositivity

/-! # Prescribed Positivity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PrescribedPositivity.CM

noncomputable section

/-! The literal prescribed source subspace is positive for its original
trace pairing. Positivity follows from the given Siegel graph. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool} (L : GeometricSource.CM.LinePeriod E B places d)

omit [IsGalois ℚ E] in
theorem position_ne_zero (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) (x : GeometricSource.CM.Ambient E)
    (hx : GeometricSource.CM.prescribed E B places d z x) (hx0 : x ≠ 0) : (L.coordinates.complex x).2 ≠ 0 := by
  intro hq
  apply hx0
  apply L.coordinates.complex.injective
  rw [map_zero]
  apply Prod.ext
  · change (L.coordinates.complex x).1 = 0
    rw [(L.graph_prescribed z hz x).mp hx, hq, Matrix.mulVec_zero]
  · exact hq

theorem positive (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) (x : GeometricSource.CM.Ambient E)
    (hx : GeometricSource.CM.prescribed E B places d z x) (hx0 : x ≠ 0) :
    0 < (ComplexPairing.CM.ambientForm E B.b L.coordinates.delta L.coordinates.a
      x (RealStructure.CM.conjugate E x)).im := by
  rw [← ComplexPairing.CM.form_equality E L.coordinates,
    ComplexPairing.CM.frameForm_apply, RealStructure.CM.frame]
  have he : Finite.TracePhase.CM.pairing (ComplexAction.CM.complexFrame E L.coordinates x)
      (fun i => star (ComplexAction.CM.complexFrame E L.coordinates x i)) =
      SiegelGraphPositivity.CM.pairing (L.coordinates.complex x).1 (L.coordinates.complex x).2 := by
    apply Finset.sum_congr rfl
    intro i _
    change (L.coordinates.complex x).1 i * star ((L.coordinates.complex x).2 i) -
      star ((L.coordinates.complex x).1 i) * (L.coordinates.complex x).2 i = _
    ring
  rw [he, (L.graph_prescribed z hz x).mp hx]
  exact SiegelGraphPositivity.CM.positive (L.period z) _ (position_ne_zero E L z hz x hx hx0)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PrescribedPositivity.CM
