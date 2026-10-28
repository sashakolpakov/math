import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PrescribedPositivity
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComponentMembership
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.MultiplierSign

/-! # Polarization Signs -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PolarizationSigns.CM

noncomputable section

/-! The actual source period determines the signs of its imaginary trace
coefficient at all selected CM places. No sign condition is added. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComponentMembership.CM.Pairing OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComponentMembership.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool} (L : GeometricSource.CM.LinePeriod E B places d)

theorem compact_selected (i : Fin places.count) (hi : i ≠ places.distinguished) :
    0 < (((ComponentMembership.CM.component E places (i, d (places.representative i)))
      (L.coordinates.delta * L.coordinates.a) : E) : ℂ).im := by
  have hp := PrescribedPositivity.CM.positive E L 0
    (MultiplierSign.CM.zero_mem_domain E) _
    (ComponentMembership.CM.compact_mem E places B d i hi 0)
    (ComponentMembership.CM.Pairing.single_ne_zero E (ComponentMembership.CM.component E places (i, d (places.representative i))) 0)
  simpa only [ComponentMembership.CM.Pairing.pairing, show (0 : Fin 3) ≠ 2 by decide, ite_false, mul_one] using hp

theorem compact_positive (i : Fin places.count) (hi : i ≠ places.distinguished)
    (hd : d (places.representative i) = false) :
    0 < (((places.representative i) (L.coordinates.delta * L.coordinates.a) : E) : ℂ).im := by
  simpa only [ComponentMembership.CM.component, hd, Bool.false_eq_true, ite_false] using compact_selected E L i hi

theorem compact_negative (i : Fin places.count) (hi : i ≠ places.distinguished)
    (hd : d (places.representative i) = true) :
    (((places.representative i) (L.coordinates.delta * L.coordinates.a) : E) : ℂ).im < 0 := by
  have hp := compact_selected E L i hi
  simp only [ComponentMembership.CM.component, hd, ite_true, AlgEquiv.mul_apply, ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_coe,
    Complex.star_def, Complex.conj_im] at hp
  exact neg_pos.mp hp

theorem distinguished_product :
    0 < (((L.coordinates.delta * L.coordinates.a : E) : ℂ) * (B.b : ℂ)).im := by
  have hp := PrescribedPositivity.CM.positive E L 0
    (MultiplierSign.CM.zero_mem_domain E) _
    (ComponentMembership.CM.distinguished_mem E places B d)
    (ComponentMembership.CM.Pairing.single_ne_zero E (ComponentMembership.CM.component E places (places.distinguished, false)) 2)
  simpa only [ComponentMembership.CM.Pairing.pairing, ComponentMembership.CM.component, Bool.false_eq_true, ite_false, places.identity,
    AlgEquiv.one_apply, ite_eq_left rfl, ite_true] using hp

theorem distinguished_negative : ((L.coordinates.delta * L.coordinates.a : E) : ℂ).im < 0 := by
  have hb : (B.b : ℂ).im = 0 := by
    have h := congrArg (fun z : E => (z : ℂ)) B.conjugate_b
    rw [ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_coe] at h
    have hi := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at hi
    linarith
  have hp := distinguished_product E L
  rw [Complex.mul_im, hb, mul_zero, zero_add] at hp
  exact (mul_pos_iff.mp hp).resolve_left (fun h => (not_lt_of_ge B.negative.le) h.2) |>.1

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PolarizationSigns.CM
