import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives

/-! # Intrinsic One -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicOne.Multiplicity

noncomputable section

/-! The native PEL coefficients satisfy the arithmetic signature inputs
for the one-line AdelicTheta construction, with the same CM representatives. -/

open scoped Classical
open _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
  (hP : P.IsAdmissible) (hμ : P.μ = E.val.toRingHom)

theorem nativePlaces_embeddings (i : Fin s) :
    HeckeCycles.ReferenceDatum.CM.embeddings E (Representatives.Multiplicity.nativePlaces E P hP hμ) i = P.embeddings i := by
  ext x
  exact Multiplicity.Period.nativeArchLabel_spec E P i x

theorem native_single_ball_negative :
    (HeckeCycles.ReferenceDatum.CM.embeddings E (Representatives.Multiplicity.nativePlaces E P hP hμ) P.distinguished P.b).re < 0 := by
  rw [nativePlaces_embeddings]
  exact hP.2.2.2.1

theorem native_single_ball_compact (i : Fin s) (hi : i ≠ P.distinguished) :
    0 < (HeckeCycles.ReferenceDatum.CM.embeddings E (Representatives.Multiplicity.nativePlaces E P hP hμ) i P.b).re := by
  rw [nativePlaces_embeddings]
  exact hP.2.2.2.2.1 i hi

theorem native_single_active_skew (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true) :
    (HeckeCycles.ReferenceDatum.CM.embeddings E (Representatives.Multiplicity.nativePlaces E P hP hμ) P.distinguished
      (P.imaginaryScalar * Multiplicity.nativeCoefficient E P v)).im < 0 := by
  rw [nativePlaces_embeddings, Multiplicity.Period.native_weight_value E P hP, Multiplicity.Period.nativeArchLabel_active E P hμ]
  exact neg_neg_of_pos (Multiplicity.Odd.imaginaryCoefficient_positive E v 1 (by simpa using hv))

theorem native_single_other_place (hs : 2 ≤ s) :
    ∃ i : Fin s, i ≠ (Representatives.Multiplicity.nativePlaces E P hP hμ).distinguished := by
  let : Nontrivial (Fin s) := Fin.nontrivial_iff_two_le.mpr hs
  exact exists_ne P.distinguished

theorem native_single_skew_sign (v : Multiplicity.Odd.Sign E) (i : Fin s) :
    (0 < (HeckeCycles.ReferenceDatum.CM.embeddings E (Representatives.Multiplicity.nativePlaces E P hP hμ) i
      (P.imaginaryScalar * Multiplicity.nativeCoefficient E P v)).im) ↔
        Multiplicity.Period.nativeCompactSigns E P v i = false := by
  rw [nativePlaces_embeddings, Multiplicity.Period.native_weight_value E P hP]
  change (0 < -((Multiplicity.Period.nativeArchLabel E P i (Multiplicity.Odd.imaginaryCoefficient E v) : E) : ℂ).im) ↔ _
  cases h : Multiplicity.Period.nativeCompactSigns E P v i
  · have hn := Multiplicity.Odd.imaginaryCoefficient_negative E v (Multiplicity.Period.nativeArchLabel E P i) h
    simp [neg_pos.mpr hn]
  · have hp := Multiplicity.Odd.imaginaryCoefficient_positive E v (Multiplicity.Period.nativeArchLabel E P i) h
    simp [not_lt.mpr (neg_nonpos.mpr hp.le)]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicOne.Multiplicity
