import OAI.NumberTheory.PadicHodge.WeakAdmissibility.DenominatorBound
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.BoundedCompletion

/-! # Comparison -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.Comparison

noncomputable section

/-!
Construction of the crystalline-to-de-Rham comparison map on the actual
p-adic completion, using the proved integral denominator bounds.
-/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaKernel OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaQuotients OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRham
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEmbedding OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEnvelope OAI.NumberTheory.PadicHodge.WeakAdmissibility.FiniteDeRhamP OAI.NumberTheory.PadicHodge.WeakAdmissibility.DenominatorBound
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.BoundedCompletion
variable (p : ℕ) [Fact p.Prime]

def integralTransition {m n : ℕ} (h : m ≤ n) :
    ThetaQuotients.ThetaPowerQuotient p n →+* ThetaQuotients.ThetaPowerQuotient p m :=
  Ideal.Quotient.factor (by
    rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
    exact Ideal.pow_le_pow_right h)

theorem integralToFinite_transition {m n : ℕ} (h : m ≤ n) (r : ThetaQuotients.ThetaPowerQuotient p n) :
    FiniteDeRhamP.integralToFinite p m (integralTransition p h r) =
      Ideal.Quotient.factorPow (DeRham.deRhamIdeal p) h (FiniteDeRhamP.integralToFinite p n r) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  rfl

def aCrisToFinite (m : ℕ) : Logarithm.PeriodRings.ACris p →+* FiniteDeRhamP.FiniteDeRham p m :=
  BoundedCompletion.boundedExtension p m (FiniteDeRhamP.integralToFinite p m) (FiniteDeRhamP.integralToFinite_injective p m)
    (FiniteDeRhamP.uncompletedToFinite p m) (DenominatorBound.uncompleted_denominator_bound p m) (FiniteDeRhamP.p_isUnit p m)

theorem aCrisToFinite_of (m : ℕ) (a : Logarithm.PeriodRings.ACrisUncompleted p) :
    aCrisToFinite p m (algebraMap (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.ACris p) a) =
      FiniteDeRhamP.uncompletedToFinite p m a :=
  BoundedCompletion.boundedExtension_of p m _ _ _ _ _ a

theorem aCrisToFinite_bound (m : ℕ) (x : Logarithm.PeriodRings.ACris p) :
    ∃ r : ThetaQuotients.ThetaPowerQuotient p m,
      FiniteDeRhamP.integralToFinite p m r = (p : FiniteDeRhamP.FiniteDeRham p m) ^ m * aCrisToFinite p m x :=
  BoundedCompletion.boundedExtension_bound p m _ _ _ _ _ x

theorem aCrisToFinite_compatible {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow (DeRham.deRhamIdeal p) h).comp (aCrisToFinite p n) =
      aCrisToFinite p m := by
  apply BoundedCompletion.bounded_hom_unique p (FiniteDeRhamP.integralToFinite p m) (FiniteDeRhamP.integralToFinite_injective p m)
    n (FiniteDeRhamP.p_isUnit p m)
  · intro a
    change Ideal.Quotient.factorPow (DeRham.deRhamIdeal p) h
      (aCrisToFinite p n (algebraMap (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.ACris p) a)) =
      aCrisToFinite p m (algebraMap (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.ACris p) a)
    rw [aCrisToFinite_of, aCrisToFinite_of]
    rfl
  · intro x
    obtain ⟨r, hr⟩ := aCrisToFinite_bound p n x
    refine ⟨integralTransition p h r, ?_⟩
    rw [integralToFinite_transition, hr, map_mul, map_pow, map_natCast]
    rfl
  · intro x
    exact BoundedCompletion.bound_mono p (FiniteDeRhamP.integralToFinite p m) h _ (aCrisToFinite_bound p m x)

/-- The completed crystalline comparison, constructed without a comparison premise. -/
def aCrisToBdRPlus : Logarithm.PeriodRings.ACris p →+* Logarithm.PeriodRings.BdRPlus p :=
  AdicCompletion.liftRingHom (DeRham.deRhamIdeal p) (aCrisToFinite p)
    (fun h => aCrisToFinite_compatible p h)

theorem aCrisToBdRPlus_eval (m : ℕ) (x : Logarithm.PeriodRings.ACris p) :
    AdicCompletion.evalₐ (DeRham.deRhamIdeal p) m (aCrisToBdRPlus p x) = aCrisToFinite p m x :=
  AdicCompletion.evalₐ_liftRingHom _ _ _ m x

theorem aCrisToBdRPlus_of (a : Logarithm.PeriodRings.ACrisUncompleted p) :
    aCrisToBdRPlus p (algebraMap (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.ACris p) a) =
      DeRhamEnvelope.uncompletedToBdRPlus p a := by
  apply AdicCompletion.ext_evalₐ
  intro m
  change AdicCompletion.evalₐ (DeRham.deRhamIdeal p) m
    (aCrisToBdRPlus p (algebraMap (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.ACris p) a)) =
    AdicCompletion.evalₐ (DeRham.deRhamIdeal p) m (DeRhamEnvelope.uncompletedToBdRPlus p a)
  rw [aCrisToBdRPlus_eval, aCrisToFinite_of]
  change FiniteDeRhamP.uncompletedToFinite p m a =
    AdicCompletion.evalₐ (DeRham.deRhamIdeal p) m
      (AdicCompletion.of (DeRham.deRhamIdeal p) (Logarithm.PeriodRings.BInf p) (DeRhamEnvelope.uncompletedToBInf p a))
  rw [AdicCompletion.evalₐ_of]
  rfl

def bCrisPlusToBdRPlus : Logarithm.PeriodRings.BCrisPlus p →+* Logarithm.PeriodRings.BdRPlus p :=
  IsLocalization.Away.lift (g := aCrisToBdRPlus p) (p : Logarithm.PeriodRings.ACris p) (by
    rw [map_natCast]
    have h : IsUnit (p : ℚ_[p]) :=
      isUnit_iff_ne_zero.mpr (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    simpa only [map_natCast] using
      h.map ((DeRham.bInfToBdRPlus p).comp (PeriodInvariants.Nontriviality.padicToBinf p)))

theorem bCrisPlusToBdRPlus_algebraMap (x : Logarithm.PeriodRings.ACris p) :
    bCrisPlusToBdRPlus p (algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p) x) = aCrisToBdRPlus p x := by
  unfold bCrisPlusToBdRPlus
  rw [IsLocalization.Away.lift_eq]

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.Comparison
