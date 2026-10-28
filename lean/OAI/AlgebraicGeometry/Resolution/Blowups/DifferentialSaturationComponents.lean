import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialSaturation
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.IntegralOpenCover
import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.ComparisonGluing
import Mathlib.RingTheory.Ideal.IdempotentFG

/-! # Differential Saturation Components -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialSaturationComponents.Construction

noncomputable section

/-! Differential saturation defines an actual smooth open-and-closed component center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) {R : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    [CommRing R] [Algebra k R] [Algebra.Smooth k R]

theorem relativeDifferentialSaturation_idempotent (J : Ideal R) :
    IsIdempotentElem (DifferentialSaturation.Construction.relativeDifferentialSaturation k J) := by
  let I := DifferentialSaturation.Construction.relativeDifferentialSaturation k J
  change I * I = I
  apply Pointed.ComparisonGluing.Construction.ideal_eq_of_pointed_flat_comparisons
  intro q hq
  let : q.IsMaximal := hq
  obtain ⟨C, hC⟩ := Blowups.Smooth.IntegralOpenCover.Construction.smooth_integral_open_chart_at_closed_point k q
  obtain ⟨P, hP⟩ : ∃ P : PrimeSpectrum C.carrier, PrimeSpectrum.comap C.map.toRingHom P = ⟨q, inferInstance⟩ := hC
  have hf : C.map.toRingHom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    (inferInstance : Etale (Spec.map (CommRingCat.ofHom C.map.toRingHom)))
  have hm : I.map C.map.toRingHom = DifferentialSaturation.Construction.relativeDifferentialSaturation k (J.map C.map.toRingHom) :=
    DifferentialSaturation.Construction.relativeDifferentialSaturation_map k C.map hf J
  have he : (I * I).map C.map.toRingHom = I.map C.map.toRingHom := by
    rw [Ideal.map_mul, hm]
    rcases DifferentialSaturation.Construction.relativeDifferentialSaturation_domain_dichotomy k (J.map C.map.toRingHom) with hz | hu
    · rw [hz, Ideal.bot_mul]
    · rw [hu, Ideal.top_mul]
  have hflat : C.map.toRingHom.Flat := by
    let : Algebra R C.carrier := C.map.toRingHom.toAlgebra
    let : Algebra.Etale R C.carrier := hf
    exact inferInstanceAs (Module.Flat R C.carrier)
  exact ⟨C.carrier, inferInstance, C.map.toRingHom, C.map.toRingHom, P.asIdeal, P.isPrime,
    hflat, congrArg PrimeSpectrum.asIdeal hP, he, rfl⟩

theorem relativeDifferentialSaturation_idempotent_generator (J : Ideal R) :
    ∃ e : R, IsIdempotentElem e ∧ DifferentialSaturation.Construction.relativeDifferentialSaturation k J = Ideal.span {e} := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have h := (Ideal.isIdempotentElem_iff_of_fg (DifferentialSaturation.Construction.relativeDifferentialSaturation k J)
    (IsNoetherian.noetherian _)).mp (relativeDifferentialSaturation_idempotent k J)
  simpa only [Ideal.submodule_span_eq] using h

theorem relativeDifferentialSaturation_quotient_etale (J : Ideal R) :
    Algebra.Etale R (R ⧸ DifferentialSaturation.Construction.relativeDifferentialSaturation k J) := by
  obtain ⟨e, he, hI⟩ := relativeDifferentialSaturation_idempotent_generator k J
  let I : Ideal R := Ideal.span {1 - (1 - e)}
  let : IsLocalization.Away (1 - e) (R ⧸ I) := IsLocalization.Away.quotient_of_isIdempotentElem he.one_sub
  let : Algebra.Etale R (R ⧸ I) := Algebra.Etale.of_isLocalizationAway (1 - e)
  have hI' : I = DifferentialSaturation.Construction.relativeDifferentialSaturation k J := by
    dsimp only [I]
    rw [sub_sub_cancel, ← hI]
  exact Algebra.Etale.of_equiv (Ideal.quotientEquivAlgOfEq R hI')

theorem relativeDifferentialSaturation_quotient_smooth (J : Ideal R) :
    Algebra.Smooth k (R ⧸ DifferentialSaturation.Construction.relativeDifferentialSaturation k J) := by
  let : Algebra.Etale R (R ⧸ DifferentialSaturation.Construction.relativeDifferentialSaturation k J) :=
    relativeDifferentialSaturation_quotient_etale k J
  exact Algebra.Smooth.comp k R _

theorem relativeDifferentialSaturation_pow_succ (J : Ideal R) (n : ℕ) :
    DifferentialSaturation.Construction.relativeDifferentialSaturation k J ^ (n + 1) = DifferentialSaturation.Construction.relativeDifferentialSaturation k J :=
  (relativeDifferentialSaturation_idempotent k J).pow_succ_eq n

theorem relativeDifferentialSaturation_permissible (J : Ideal R) (b : ℕ) :
    J ≤ DifferentialSaturation.Construction.relativeDifferentialSaturation k J ^ b := by
  cases b with
  | zero =>
      rw [pow_zero, Ideal.one_eq_top]
      exact (le_top : J ≤ (⊤ : Ideal R))
  | succ n =>
      rw [relativeDifferentialSaturation_pow_succ]
      exact DifferentialSaturation.Construction.le_relativeDifferentialSaturation k J

end

end OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialSaturationComponents.Construction
