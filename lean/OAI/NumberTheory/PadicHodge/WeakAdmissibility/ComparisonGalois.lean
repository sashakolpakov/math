import OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonBd
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.Galois

/-! # Comparison Galois -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonGalois

noncomputable section

/-! Galois equivariance of the constructed completed comparison. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaKernel OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaQuotients OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRham OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEnvelope
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.FiniteDeRhamP OAI.NumberTheory.PadicHodge.WeakAdmissibility.Comparison OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonBd OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamDVR
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Galois OAI.NumberTheory.PadicHodge.WeakAdmissibility.BoundedCompletion
variable (p : ℕ) [Fact p.Prime]

theorem aInfMap_preserves_theta (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) :
    (RingHom.ker (Logarithm.PeriodRings.theta p)).map (PeriodInvariants.PeriodRing.ainfMap p f) ≤ RingHom.ker (Logarithm.PeriodRings.theta p) := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change Logarithm.PeriodRings.theta p (PeriodInvariants.PeriodRing.ainfMap p f x) = 0
  have he := PeriodInvariants.PeriodRing.theta_natural p f x
  change Logarithm.PeriodRings.theta p (PeriodInvariants.PeriodRing.ainfMap p f x) = f (Logarithm.PeriodRings.theta p x) at he
  rw [he, RingHom.mem_ker.mp hx, map_zero]

def integralMap (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (m : ℕ) :
    ThetaQuotients.ThetaPowerQuotient p m →+* ThetaQuotients.ThetaPowerQuotient p m :=
  Ideal.quotientMap _ (PeriodInvariants.PeriodRing.ainfMap p f) (by
    have h := Logarithm.PeriodRings.map_preserves_ideal_pow (RingHom.ker (Logarithm.PeriodRings.theta p)) (PeriodInvariants.PeriodRing.ainfMap p f)
      (aInfMap_preserves_theta p f) m
    rwa [ThetaKernel.theta_kernel_eq_span, Ideal.span_singleton_pow] at h)

def finiteMap (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (m : ℕ) : FiniteDeRhamP.FiniteDeRham p m →+* FiniteDeRhamP.FiniteDeRham p m :=
  Ideal.quotientMap _ (DeRham.bInfMap p f)
    (Logarithm.PeriodRings.map_preserves_ideal_pow (DeRham.deRhamIdeal p) (DeRham.bInfMap p f) (DeRham.bInfMap_preserves_deRhamIdeal p f) m)

theorem integralToFinite_natural (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (m : ℕ) (r : ThetaQuotients.ThetaPowerQuotient p m) :
    FiniteDeRhamP.integralToFinite p m (integralMap p f m r) = finiteMap p f m (FiniteDeRhamP.integralToFinite p m r) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  change Ideal.Quotient.mk _ (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p) (PeriodInvariants.PeriodRing.ainfMap p f a)) =
    Ideal.Quotient.mk _ (DeRham.bInfMap p f (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p) a))
  rw [DeRham.bInfMap_algebraMap]

theorem bInfMap_fraction (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : Logarithm.PeriodRings.BInf p) :
    PeriodInvariants.Nontriviality.binfToFraction p (DeRham.bInfMap p f.toRingHom x) =
      PeriodInvariants.PeriodRing.ainfFractionEquiv p f (PeriodInvariants.Nontriviality.binfToFraction p x) := by
  have he : (PeriodInvariants.Nontriviality.binfToFraction p).comp (DeRham.bInfMap p f.toRingHom) =
      (PeriodInvariants.PeriodRing.ainfFractionEquiv p f).toRingHom.comp (PeriodInvariants.Nontriviality.binfToFraction p) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : Logarithm.PeriodRings.AInf p))
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply, DeRham.bInfMap_algebraMap, PeriodInvariants.Nontriviality.binfToFraction_algebraMap,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, PeriodInvariants.PeriodRing.ainfFractionEquiv_algebraMap]
  exact DFunLike.congr_fun he x

theorem uncompletedToBInf_natural (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : Logarithm.PeriodRings.ACrisUncompleted p) :
    DeRhamEnvelope.uncompletedToBInf p (Galois.uncompletedMap p f x) = DeRham.bInfMap p f.toRingHom (DeRhamEnvelope.uncompletedToBInf p x) := by
  apply PeriodInvariants.Nontriviality.binfToFraction_injective p
  rw [DeRhamEnvelope.uncompletedToBInf_fraction, bInfMap_fraction, DeRhamEnvelope.uncompletedToBInf_fraction]
  rfl

theorem aCrisToFinite_natural (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (m : ℕ) :
    (Comparison.aCrisToFinite p m).comp (Galois.completedMap p f) =
      (finiteMap p f.toRingHom m).comp (Comparison.aCrisToFinite p m) := by
  apply BoundedCompletion.bounded_hom_unique p (FiniteDeRhamP.integralToFinite p m) (FiniteDeRhamP.integralToFinite_injective p m)
    m (FiniteDeRhamP.p_isUnit p m)
  · intro a
    change Comparison.aCrisToFinite p m (Logarithm.PeriodRings.completionMap _ (Galois.uncompletedMap p f) _
      (AdicCompletion.of _ (Logarithm.PeriodRings.ACrisUncompleted p) a)) =
      finiteMap p f.toRingHom m (Comparison.aCrisToFinite p m (AdicCompletion.of _ (Logarithm.PeriodRings.ACrisUncompleted p) a))
    rw [Logarithm.PeriodRings.completionMap_of]
    change Comparison.aCrisToFinite p m (algebraMap (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.ACris p) (Galois.uncompletedMap p f a)) =
      finiteMap p f.toRingHom m (Comparison.aCrisToFinite p m (algebraMap (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.ACris p) a))
    rw [Comparison.aCrisToFinite_of, Comparison.aCrisToFinite_of]
    change Ideal.Quotient.mk _ (DeRhamEnvelope.uncompletedToBInf p (Galois.uncompletedMap p f a)) =
      Ideal.Quotient.mk _ (DeRham.bInfMap p f.toRingHom (DeRhamEnvelope.uncompletedToBInf p a))
    rw [uncompletedToBInf_natural]
  · intro x
    exact Comparison.aCrisToFinite_bound p m (Galois.completedMap p f x)
  · intro x
    obtain ⟨r, hr⟩ := Comparison.aCrisToFinite_bound p m x
    refine ⟨integralMap p f.toRingHom m r, ?_⟩
    rw [integralToFinite_natural, hr, map_mul, map_pow, map_natCast]
    rfl

theorem aCrisToBdRPlus_natural (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : Logarithm.PeriodRings.ACris p) :
    Comparison.aCrisToBdRPlus p (Galois.completedMap p f x) = DeRham.bdRPlusMap p f.toRingHom (Comparison.aCrisToBdRPlus p x) := by
  apply AdicCompletion.ext_evalₐ
  intro m
  change AdicCompletion.evalₐ (DeRham.deRhamIdeal p) m (Comparison.aCrisToBdRPlus p (Galois.completedMap p f x)) =
    AdicCompletion.evalₐ (DeRham.deRhamIdeal p) m (Logarithm.PeriodRings.completionMap (DeRham.deRhamIdeal p) (DeRham.bInfMap p f.toRingHom) _
      (Comparison.aCrisToBdRPlus p x))
  rw [Comparison.aCrisToBdRPlus_eval, Logarithm.PeriodRings.completionMap]
  erw [AdicCompletion.evalₐ_liftRingHom]
  change Comparison.aCrisToFinite p m (Galois.completedMap p f x) =
    finiteMap p f.toRingHom m (AdicCompletion.evalₐ (DeRham.deRhamIdeal p) m (Comparison.aCrisToBdRPlus p x))
  rw [Comparison.aCrisToBdRPlus_eval]
  exact DFunLike.congr_fun (aCrisToFinite_natural p f m) x

theorem bCrisPlusToBdRPlus_natural (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : Logarithm.PeriodRings.BCrisPlus p) :
    Comparison.bCrisPlusToBdRPlus p (Galois.positiveMap p f x) = DeRham.bdRPlusMap p f.toRingHom (Comparison.bCrisPlusToBdRPlus p x) := by
  have he : (Comparison.bCrisPlusToBdRPlus p).comp (Galois.positiveMap p f) =
      (DeRham.bdRPlusMap p f.toRingHom).comp (Comparison.bCrisPlusToBdRPlus p) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : Logarithm.PeriodRings.ACris p))
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply, Galois.positiveMap_algebraMap, Comparison.bCrisPlusToBdRPlus_algebraMap]
    exact aCrisToBdRPlus_natural p f a
  exact DFunLike.congr_fun he x

def completionGaloisAction : PeriodInvariants.PeriodRing.PadicGalois p →*
    (DeRhamDVR.DeRhamCompletion p ≃+* DeRhamDVR.DeRhamCompletion p) := DeRham.galoisBdRPlusAction p

/-- The genuine action on the de Rham fraction field. -/
def galoisBdRAction : PeriodInvariants.PeriodRing.PadicGalois p →* (Logarithm.PeriodRings.BdR p ≃+* Logarithm.PeriodRings.BdR p) :=
  (IsFractionRing.ringEquivOfRingEquivHom (DeRhamDVR.DeRhamCompletion p) (Logarithm.PeriodRings.BdR p)).comp (completionGaloisAction p)

theorem galoisBdRAction_of (σ : PeriodInvariants.PeriodRing.PadicGalois p) (x : Logarithm.PeriodRings.BdRPlus p) :
    galoisBdRAction p σ (ComparisonBd.bdRPlusToBdR p x) =
      ComparisonBd.bdRPlusToBdR p (DeRham.galoisBdRPlusAction p σ x) := by
  change IsFractionRing.ringEquivOfRingEquiv (completionGaloisAction p σ)
    (algebraMap (DeRhamDVR.DeRhamCompletion p) (Logarithm.PeriodRings.BdR p) x) = _
  erw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  rfl

theorem bCrisPlusToBdR_galois (σ : PeriodInvariants.PeriodRing.PadicGalois p) (x : Logarithm.PeriodRings.BCrisPlus p) :
    ComparisonBd.bCrisPlusToBdR p (Galois.positiveMap p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ) x) =
      galoisBdRAction p σ (ComparisonBd.bCrisPlusToBdR p x) := by
  change ComparisonBd.bdRPlusToBdR p (Comparison.bCrisPlusToBdRPlus p (Galois.positiveMap p _ x)) =
    galoisBdRAction p σ (ComparisonBd.bdRPlusToBdR p (Comparison.bCrisPlusToBdRPlus p x))
  rw [galoisBdRAction_of, bCrisPlusToBdRPlus_natural]
  rfl

/-- The full comparison is equivariant for the actual absolute Galois actions. -/
theorem bCrisToBdR_galois (σ : PeriodInvariants.PeriodRing.PadicGalois p) (x : Logarithm.PeriodRings.BCris p) :
    ComparisonBd.bCrisToBdR p (Galois.galoisBCrisMap p σ x) = galoisBdRAction p σ (ComparisonBd.bCrisToBdR p x) := by
  have he : (ComparisonBd.bCrisToBdR p).comp (Galois.galoisBCrisMap p σ) =
      (galoisBdRAction p σ).toRingHom.comp (ComparisonBd.bCrisToBdR p) := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers (algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.cyclotomicPeriod p)))
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply, Galois.galoisBCrisMap_algebraMap, ComparisonBd.bCrisToBdR_algebraMap,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    exact bCrisPlusToBdR_galois p σ a
  exact DFunLike.congr_fun he x

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonGalois
