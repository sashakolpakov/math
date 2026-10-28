import OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteLattices
import OAI.NumberTheory.PadicHodge.PeriodInvariants.AdditiveCompletion

/-! # Finite Comparison -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.PeriodInvariants.FiniteComparison

/-!
# The crystalline map to each finite de Rham quotient

The factorial bound gives an additive map into a complete integral lattice.
Its multiplication identity extends through completion. Dividing by the
factorial then gives an actual ring map from A_cris to each rational quotient.
-/

section Normalization

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Remove an invertible scalar from an additive map with the scaled ring identities. -/
def normalizeScaledAddMap (f : R →+ S) (u : Sˣ) (h1 : f 1 = u)
    (hmul : ∀ x y : R, (u : S) * f (x * y) = f x * f y) : R →+* S where
  toFun x := (u⁻¹ : Sˣ) * f x
  map_zero' := by rw [map_zero, mul_zero]
  map_add' x y := by rw [map_add, mul_add]
  map_one' := by rw [h1, Units.inv_mul]
  map_mul' x y := by
    calc
      (↑u⁻¹ : S) * f (x * y) = (↑u⁻¹ : S) * ((↑u⁻¹ : S) * ((u : S) * f (x * y))) := by
        rw [Units.inv_mul_cancel_left]
      _ = (↑u⁻¹ : S) * ((↑u⁻¹ : S) * (f x * f y)) := by rw [hmul]
      _ = _ := by ring

theorem normalizeScaledAddMap_spec (f : R →+ S) (u : Sˣ) (h1 : f 1 = u)
    (hmul : ∀ x y : R, (u : S) * f (x * y) = f x * f y) (x : R) :
    (u : S) * normalizeScaledAddMap f u h1 hmul x = f x := by
  change (u : S) * ((↑u⁻¹ : S) * f x) = f x
  rw [← mul_assoc, Units.mul_inv, one_mul]

end Normalization

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.PrincipalEnvelope OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteLattices.Period OAI.NumberTheory.PadicHodge.PeriodInvariants.AdditiveCompletion

variable (p : ℕ) [Fact p.Prime]

def integralLift (N : ℕ) (x : PeriodRing.AcrisZero p) : FiniteLattices.Period.IntegralQuotient p N :=
  Ideal.Quotient.mk _ (FiniteLattices.Period.factorial_projection_integral p N x).choose

theorem integralLift_spec (N : ℕ) (x : PeriodRing.AcrisZero p) :
    algebraMap (FiniteLattices.Period.IntegralQuotient p N) (FiniteLattices.Period.RationalQuotient p N) (integralLift p N x) =
      (N.factorial : FiniteLattices.Period.RationalQuotient p N) * FiniteLattices.Period.envelopeProjection p N x := by
  have he := IsScalarTower.algebraMap_apply (PeriodRing.Ainf p) (FiniteLattices.Period.IntegralQuotient p N)
    (FiniteLattices.Period.RationalQuotient p N) (FiniteLattices.Period.factorial_projection_integral p N x).choose
  rw [Ideal.Quotient.algebraMap_eq] at he
  exact he.symm.trans (FiniteLattices.Period.factorial_projection_integral p N x).choose_spec

def integralLiftAddMap (N : ℕ) : PeriodRing.AcrisZero p →+ FiniteLattices.Period.IntegralQuotient p N where
  toFun := integralLift p N
  map_zero' := by
    apply FiniteLattices.Period.integralQuotient_injective p N
    rw [integralLift_spec, map_zero, map_zero, mul_zero]
  map_add' x y := by
    apply FiniteLattices.Period.integralQuotient_injective p N
    simp only [map_add, integralLift_spec, mul_add]

theorem integralLiftAddMap_one (N : ℕ) : integralLiftAddMap p N 1 = (N.factorial : FiniteLattices.Period.IntegralQuotient p N) := by
  apply FiniteLattices.Period.integralQuotient_injective p N
  change algebraMap _ _ (integralLift p N 1) = _
  rw [integralLift_spec, map_one, mul_one, map_natCast]

theorem integralLiftAddMap_mul (N : ℕ) (x y : PeriodRing.AcrisZero p) :
    (N.factorial : FiniteLattices.Period.IntegralQuotient p N) * integralLiftAddMap p N (x * y) =
      integralLiftAddMap p N x * integralLiftAddMap p N y := by
  apply FiniteLattices.Period.integralQuotient_injective p N
  change algebraMap _ _ ((N.factorial : FiniteLattices.Period.IntegralQuotient p N) * integralLift p N (x * y)) =
    algebraMap _ _ (integralLift p N x * integralLift p N y)
  simp only [map_mul, map_natCast, integralLift_spec]
  ring

def completedScaledProjection (N : ℕ) : PeriodRing.Acris p →+ FiniteLattices.Period.RationalQuotient p N :=
  (algebraMap (FiniteLattices.Period.IntegralQuotient p N) (FiniteLattices.Period.RationalQuotient p N)).toAddMonoidHom.comp
    (AdditiveCompletion.extendAddMap p (integralLiftAddMap p N))

theorem completedScaledProjection_of (N : ℕ) (x : PeriodRing.AcrisZero p) :
    completedScaledProjection p N (AdicCompletion.of (Ideal.span {(p : PeriodRing.AcrisZero p)}) _ x) =
      (N.factorial : FiniteLattices.Period.RationalQuotient p N) * FiniteLattices.Period.envelopeProjection p N x := by
  change algebraMap (FiniteLattices.Period.IntegralQuotient p N) (FiniteLattices.Period.RationalQuotient p N)
    (AdditiveCompletion.extendAddMap p (integralLiftAddMap p N) _) = _
  rw [AdditiveCompletion.extendAddMap_of]
  exact integralLift_spec p N x

theorem completedScaledProjection_one (N : ℕ) :
    completedScaledProjection p N 1 = (N.factorial : FiniteLattices.Period.RationalQuotient p N) := by
  have h := completedScaledProjection_of p N 1
  have hone : AdicCompletion.of (Ideal.span {(p : PeriodRing.AcrisZero p)}) (PeriodRing.AcrisZero p) 1 = (1 : PeriodRing.Acris p) :=
    (algebraMap (PeriodRing.AcrisZero p) (PeriodRing.Acris p)).map_one
  have he : FiniteLattices.Period.envelopeProjection p N 1 = 1 := map_one _
  rw [hone, he, mul_one] at h
  exact h

theorem completedScaledProjection_mul (N : ℕ) (x y : PeriodRing.Acris p) :
    (N.factorial : FiniteLattices.Period.RationalQuotient p N) * completedScaledProjection p N (x * y) =
      completedScaledProjection p N x * completedScaledProjection p N y := by
  have h := congrArg (algebraMap (FiniteLattices.Period.IntegralQuotient p N) (FiniteLattices.Period.RationalQuotient p N))
    (AdditiveCompletion.extendAddMap_scaled_mul p (integralLiftAddMap p N) N.factorial
      (integralLiftAddMap_mul p N) x y)
  simp only [map_mul, map_natCast] at h
  exact h

/-- The actual map from the completed crystalline envelope to a finite de Rham quotient. -/
def acrisToFiniteQuotient (N : ℕ) : PeriodRing.Acris p →+* FiniteLattices.Period.RationalQuotient p N :=
  normalizeScaledAddMap (completedScaledProjection p N) (FiniteLattices.Period.factorial_unit p N N).unit
    (by rw [(FiniteLattices.Period.factorial_unit p N N).unit_spec]; exact completedScaledProjection_one p N)
    (by rw [(FiniteLattices.Period.factorial_unit p N N).unit_spec]; exact completedScaledProjection_mul p N)

theorem acrisToFiniteQuotient_scaled (N : ℕ) (x : PeriodRing.Acris p) :
    (N.factorial : FiniteLattices.Period.RationalQuotient p N) * acrisToFiniteQuotient p N x =
      completedScaledProjection p N x := by
  have h := normalizeScaledAddMap_spec (completedScaledProjection p N)
    (FiniteLattices.Period.factorial_unit p N N).unit
    (by rw [(FiniteLattices.Period.factorial_unit p N N).unit_spec]; exact completedScaledProjection_one p N)
    (by rw [(FiniteLattices.Period.factorial_unit p N N).unit_spec]; exact completedScaledProjection_mul p N) x
  change ((FiniteLattices.Period.factorial_unit p N N).unit : FiniteLattices.Period.RationalQuotient p N) *
    acrisToFiniteQuotient p N x = completedScaledProjection p N x at h
  rw [(FiniteLattices.Period.factorial_unit p N N).unit_spec] at h
  exact h

/-- The completed map agrees with the original divided-power envelope map. -/
theorem acrisToFiniteQuotient_of (N : ℕ) (x : PeriodRing.AcrisZero p) :
    acrisToFiniteQuotient p N (AdicCompletion.of (Ideal.span {(p : PeriodRing.AcrisZero p)}) _ x) =
      FiniteLattices.Period.envelopeProjection p N x := by
  apply (FiniteLattices.Period.factorial_unit p N N).mul_left_cancel
  rw [acrisToFiniteQuotient_scaled, completedScaledProjection_of]

end NumberTheory.PadicHodge.PeriodInvariants.FiniteComparison

namespace NumberTheory.PadicHodge.PeriodInvariants.FiniteComparison.Compatibility

/-!
# Compatibility of the finite crystalline maps

The integral identities use both factorial bounds. Additive completion
preserves those identities, and the factorials cancel in the rational quotients.
-/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.ThetaKernel OAI.NumberTheory.PadicHodge.PeriodInvariants.Nontriviality OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteLattices.Period
  FiniteComparison AdditiveCompletion

variable (p : ℕ) [Fact p.Prime]

theorem thetaPower_le {M N : ℕ} (h : M ≤ N) :
    (Ideal.span {ThetaKernel.xi p ^ N} : Ideal (PeriodRing.Ainf p)) ≤ Ideal.span {ThetaKernel.xi p ^ M} := by
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
  exact pow_dvd_pow (ThetaKernel.xi p) h

def integralTransition {M N : ℕ} (h : M ≤ N) : FiniteLattices.Period.IntegralQuotient p N →+* FiniteLattices.Period.IntegralQuotient p M :=
  Ideal.Quotient.factor (thetaPower_le p h)

def rationalTransition {M N : ℕ} (h : M ≤ N) : FiniteLattices.Period.RationalQuotient p N →+* FiniteLattices.Period.RationalQuotient p M :=
  Ideal.Quotient.factor (Ideal.map_mono (thetaPower_le p h))

theorem integral_embed_mk (N : ℕ) (a : PeriodRing.Ainf p) :
    algebraMap (FiniteLattices.Period.IntegralQuotient p N) (FiniteLattices.Period.RationalQuotient p N) (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (algebraMap (PeriodRing.Ainf p) (Nontriviality.Binf p) a) := by
  have h := IsScalarTower.algebraMap_apply (PeriodRing.Ainf p) (FiniteLattices.Period.IntegralQuotient p N) (FiniteLattices.Period.RationalQuotient p N) a
  rw [Ideal.Quotient.algebraMap_eq] at h
  have h' := IsScalarTower.algebraMap_apply (PeriodRing.Ainf p) (Nontriviality.Binf p) (FiniteLattices.Period.RationalQuotient p N) a
  rw [Ideal.Quotient.algebraMap_eq] at h'
  exact h.symm.trans h'

theorem transition_embed {M N : ℕ} (h : M ≤ N) (x : FiniteLattices.Period.IntegralQuotient p N) :
    rationalTransition p h (algebraMap (FiniteLattices.Period.IntegralQuotient p N) (FiniteLattices.Period.RationalQuotient p N) x) =
      algebraMap (FiniteLattices.Period.IntegralQuotient p M) (FiniteLattices.Period.RationalQuotient p M) (integralTransition p h x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [integral_embed_mk]
  change Ideal.Quotient.mk _ (algebraMap (PeriodRing.Ainf p) (Nontriviality.Binf p) a) =
    algebraMap (FiniteLattices.Period.IntegralQuotient p M) (FiniteLattices.Period.RationalQuotient p M) (Ideal.Quotient.mk _ a)
  exact (integral_embed_mk p M a).symm

theorem transition_envelopeProjection {M N : ℕ} (h : M ≤ N) (x : PeriodRing.AcrisZero p) :
    rationalTransition p h (FiniteLattices.Period.envelopeProjection p N x) = FiniteLattices.Period.envelopeProjection p M x := rfl

theorem integralLift_transition {M N : ℕ} (h : M ≤ N) (x : PeriodRing.AcrisZero p) :
    (M.factorial : FiniteLattices.Period.IntegralQuotient p M) * integralTransition p h (integralLiftAddMap p N x) =
      (N.factorial : FiniteLattices.Period.IntegralQuotient p M) * integralLiftAddMap p M x := by
  apply FiniteLattices.Period.integralQuotient_injective p M
  simp only [map_mul, map_natCast]
  rw [← transition_embed]
  change (M.factorial : FiniteLattices.Period.RationalQuotient p M) * rationalTransition p h
      (algebraMap (FiniteLattices.Period.IntegralQuotient p N) (FiniteLattices.Period.RationalQuotient p N) (integralLift p N x)) =
    (N.factorial : FiniteLattices.Period.RationalQuotient p M) *
      algebraMap (FiniteLattices.Period.IntegralQuotient p M) (FiniteLattices.Period.RationalQuotient p M) (integralLift p M x)
  rw [integralLift_spec, integralLift_spec, map_mul, map_natCast, transition_envelopeProjection]
  ring

theorem completedScaledProjection_transition {M N : ℕ} (h : M ≤ N) (x : PeriodRing.Acris p) :
    (M.factorial : FiniteLattices.Period.RationalQuotient p M) * rationalTransition p h (completedScaledProjection p N x) =
      (N.factorial : FiniteLattices.Period.RationalQuotient p M) * completedScaledProjection p M x := by
  have he := AdditiveCompletion.extendAddMap_scaled_natural p (integralLiftAddMap p N) (integralLiftAddMap p M)
    (integralTransition p h).toAddMonoidHom M.factorial N.factorial (integralLift_transition p h) x
  have he' := congrArg (algebraMap (FiniteLattices.Period.IntegralQuotient p M) (FiniteLattices.Period.RationalQuotient p M)) he
  simp only [map_mul, map_natCast] at he'
  change (M.factorial : FiniteLattices.Period.RationalQuotient p M) *
      algebraMap (FiniteLattices.Period.IntegralQuotient p M) (FiniteLattices.Period.RationalQuotient p M)
        (integralTransition p h (AdditiveCompletion.extendAddMap p (integralLiftAddMap p N) x)) =
    (N.factorial : FiniteLattices.Period.RationalQuotient p M) *
      algebraMap (FiniteLattices.Period.IntegralQuotient p M) (FiniteLattices.Period.RationalQuotient p M)
        (AdditiveCompletion.extendAddMap p (integralLiftAddMap p M) x) at he'
  rw [← transition_embed] at he'
  exact he'

/-- The constructed crystalline maps agree at every common finite precision. -/
theorem acrisToFiniteQuotient_compatible {M N : ℕ} (h : M ≤ N) (x : PeriodRing.Acris p) :
    rationalTransition p h (acrisToFiniteQuotient p N x) = acrisToFiniteQuotient p M x := by
  apply (FiniteLattices.Period.factorial_unit p M M).mul_left_cancel
  apply (FiniteLattices.Period.factorial_unit p M N).mul_left_cancel
  calc
    (N.factorial : FiniteLattices.Period.RationalQuotient p M) *
        ((M.factorial : FiniteLattices.Period.RationalQuotient p M) * rationalTransition p h (acrisToFiniteQuotient p N x)) =
        (M.factorial : FiniteLattices.Period.RationalQuotient p M) * rationalTransition p h
          ((N.factorial : FiniteLattices.Period.RationalQuotient p N) * acrisToFiniteQuotient p N x) := by
      rw [map_mul, map_natCast]
      ring
    _ = (M.factorial : FiniteLattices.Period.RationalQuotient p M) * rationalTransition p h (completedScaledProjection p N x) := by
      rw [acrisToFiniteQuotient_scaled]
    _ = (N.factorial : FiniteLattices.Period.RationalQuotient p M) * completedScaledProjection p M x :=
      completedScaledProjection_transition p h x
    _ = (N.factorial : FiniteLattices.Period.RationalQuotient p M) *
        ((M.factorial : FiniteLattices.Period.RationalQuotient p M) * acrisToFiniteQuotient p M x) := by
      rw [acrisToFiniteQuotient_scaled]

end NumberTheory.PadicHodge.PeriodInvariants.FiniteComparison.Compatibility

end

end OAI
