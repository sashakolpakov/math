import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.AuxiliaryIdeal
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Localization.Away.Lemmas
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # Zero Dimensional Coefficient Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ZeroDimensionalCoefficientCenter.Construction

noncomputable section

/-! A complete self-center step for coefficient ideals in reduced dimension zero. -/

variable {H : Type*} [CommRing H] [IsNoetherianRing H] [IsReduced H]

/-- Every ideal on a reduced Noetherian ring of dimension zero is generated
by an actual idempotent. This includes the zero ideal and disconnected rings. -/
theorem zero_dimensional_ideal_idempotent_generator (hd : ringKrullDim H ≤ 0) (C : Ideal H) :
    ∃ e : H, IsIdempotentElem e ∧ C = Ideal.span {e} := by
  let : Ring.KrullDimLE 0 H := Ring.krullDimLE_iff.mpr hd
  let : IsArtinianRing H := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  let : IsSemisimpleRing H := IsArtinianRing.isSemisimpleRing_of_isReduced H
  exact IsSemisimpleRing.ideal_eq_span_idempotent C

theorem zero_dimensional_ideal_pow (hd : ringKrullDim H ≤ 0) (C : Ideal H) (n : ℕ) :
    C ^ (n + 1) = C := by
  obtain ⟨e, he, hC⟩ := zero_dimensional_ideal_idempotent_generator hd C
  rw [hC, Ideal.span_singleton_pow, he.pow_succ_eq n]

theorem zero_dimensional_ideal_isRadical (hd : ringKrullDim H ≤ 0) (C : Ideal H) : C.IsRadical := by
  let : Ring.KrullDimLE 0 H := Ring.krullDimLE_iff.mpr hd
  let : IsArtinianRing H := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  let : IsSemisimpleRing H := IsArtinianRing.isSemisimpleRing_of_isReduced H
  let : IsSemisimpleRing (H ⧸ C) := RingHom.isSemisimpleRing_of_surjective
    (Ideal.Quotient.mk C) Ideal.Quotient.mk_surjective
  exact (Ideal.isRadical_iff_quotient_reduced C).mpr inferInstance

/-- The corresponding closed center is also open: its quotient is an
actual localization, hence étale over the zero-dimensional ambient ring. -/
theorem zero_dimensional_ideal_quotient_etale (hd : ringKrullDim H ≤ 0) (C : Ideal H) :
    Algebra.Etale H (H ⧸ C) := by
  obtain ⟨e, he, hC⟩ := zero_dimensional_ideal_idempotent_generator hd C
  let J : Ideal H := Ideal.span {1 - (1 - e)}
  let : IsLocalization.Away (1 - e) (H ⧸ J) := IsLocalization.Away.quotient_of_isIdempotentElem he.one_sub
  let : Algebra.Etale H (H ⧸ J) := Algebra.Etale.of_isLocalizationAway (1 - e)
  have hJ : J = C := by
    dsimp only [J]
    rw [sub_sub_cancel, ← hC]
  exact Algebra.Etale.of_equiv (Ideal.quotientEquivAlgOfEq H hJ)

variable (k : Type*) [CommRing k] [Algebra k H] [Algebra.Smooth k H]

/-- The coefficient ideal itself defines a smooth permissible center for
every positive control, and its actual controlled ideal is the unit ideal
on every affine chart of its blowup. -/
theorem zero_dimensional_coefficient_self_center (hd : ringKrullDim H ≤ 0)
    (C : Ideal H) (n : ℕ) :
    C ≤ C ^ (n + 1) ∧ Algebra.Smooth k (H ⧸ C) ∧
      ∀ a : C, ControlledTransform.Construction.blowupControlledTransform C C (n + 1) a = ⊤ := by
  let : Algebra.Etale H (H ⧸ C) := zero_dimensional_ideal_quotient_etale hd C
  refine ⟨(zero_dimensional_ideal_pow hd C n).symm.le, Algebra.Smooth.comp k H (H ⧸ C), ?_⟩
  intro a
  apply Boundary.AuxiliaryIdeal.Construction.blowupControlledTransform_eq_top_of_parameter_power C C a (n + 1)
  rw [pow_succ]
  exact C.mul_mem_left (a.val ^ n) a.property

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ZeroDimensionalCoefficientCenter.Construction
