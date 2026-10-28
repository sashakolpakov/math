import OAI.NumberTheory.PadicHodge.WeakAdmissibility.PrimitiveElements
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamDVR
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamLog

/-! # Period Uniformizer -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.PeriodUniformizer

noncomputable section

/-! The actual cyclotomic logarithm has de Rham filtration degree exactly one. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaKernel OAI.NumberTheory.PadicHodge.WeakAdmissibility.PrimitiveElements OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRham OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEmbedding
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEmbedding.Residue OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamDVR OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamLog OAI.NumberTheory.PadicHodge.WeakAdmissibility.Comparison
variable (p : ℕ) [Fact p.Prime]

def epsilonRoot : PreTilt 𝓞_ℂ_[p] p :=
  PeriodInvariants.PeriodRing.tiltMonoidEquiv p (Perfection.pthRootMonoidHom 𝓞_ℂ_[p] p (Logarithm.PeriodRings.cyclotomicTower p))

theorem epsilonRoot_untilt : (epsilonRoot p).untilt = Logarithm.PeriodRings.firstCyclotomicInteger p := by
  rw [epsilonRoot, PeriodInvariants.PeriodRing.untilt_tiltMonoidEquiv]
  rfl

theorem epsilonRoot_pow : epsilonRoot p ^ p = Logarithm.PeriodRings.epsilon p := by
  rw [epsilonRoot, ← map_pow]
  have he : (Perfection.pthRootMonoidHom 𝓞_ℂ_[p] p (Logarithm.PeriodRings.cyclotomicTower p)) ^ p = Logarithm.PeriodRings.cyclotomicTower p := by
    apply Perfection.extMonoid
    intro n
    rw [map_pow, Perfection.coeffMonoidHom_pthRootMonoidHom]
    exact (Logarithm.PeriodRings.cyclotomicTower p).property n
  rw [he]
  rfl

theorem epsilonRoot_residue : PrimitiveElements.tiltResidue p (epsilonRoot p) = 1 := by
  rw [PrimitiveElements.tiltResidue_untilt, epsilonRoot_untilt]
  apply frobenius_inj (PrimitiveElements.ResidueCp p) p
  change IsLocalRing.residue 𝓞_ℂ_[p] (Logarithm.PeriodRings.firstCyclotomicInteger p) ^ p = (1 : PrimitiveElements.ResidueCp p) ^ p
  rw [← map_pow, Logarithm.PeriodRings.firstCyclotomicInteger_pow, map_one, one_pow]

def cyclotomicKernelGenerator : Logarithm.PeriodRings.AInf p :=
  ∑ i ∈ Finset.range p, WittVector.teichmuller p (epsilonRoot p) ^ i

theorem theta_epsilonRoot_teich :
    Logarithm.PeriodRings.theta p (WittVector.teichmuller p (epsilonRoot p)) = Logarithm.PeriodRings.firstCyclotomicInteger p := by
  rw [Logarithm.PeriodRings.theta, WittVector.fontaineTheta_teichmuller, epsilonRoot_untilt]

theorem cyclotomicKernelGenerator_theta : Logarithm.PeriodRings.theta p (cyclotomicKernelGenerator p) = 0 := by
  rw [cyclotomicKernelGenerator, map_sum]
  simp only [map_pow, theta_epsilonRoot_teich]
  apply mul_right_cancel₀ (sub_ne_zero.mpr (Logarithm.PeriodRings.firstCyclotomicInteger_ne_one p))
  rw [zero_mul, geom_sum_mul, Logarithm.PeriodRings.firstCyclotomicInteger_pow, sub_self]

theorem cyclotomicKernelGenerator_residue :
    PrimitiveElements.wittResidue p (cyclotomicKernelGenerator p) = (p : WittVector p (PrimitiveElements.ResidueCp p)) := by
  rw [cyclotomicKernelGenerator, map_sum]
  simp only [map_pow]
  have he : PrimitiveElements.wittResidue p (WittVector.teichmuller p (epsilonRoot p)) = 1 := by
    change WittVector.map (PrimitiveElements.tiltResidue p) (WittVector.teichmuller p (epsilonRoot p)) = 1
    rw [WittVector.map_teichmuller, epsilonRoot_residue, map_one]
  simp only [he, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

theorem theta_kernel_cyclotomic_generator :
    RingHom.ker (Logarithm.PeriodRings.theta p) = Ideal.span {cyclotomicKernelGenerator p} :=
  PrimitiveElements.theta_generator_of_residue_p p _ (cyclotomicKernelGenerator_theta p) (cyclotomicKernelGenerator_residue p)

theorem cyclotomicDifference_factor : Logarithm.PeriodRings.cyclotomicDifference p =
    cyclotomicKernelGenerator p * (WittVector.teichmuller p (epsilonRoot p) - 1) := by
  rw [cyclotomicKernelGenerator, geom_sum_mul, ← map_pow, epsilonRoot_pow]
  rfl

theorem deRhamIdeal_cyclotomic_generator : DeRham.deRhamIdeal p =
    Ideal.span {algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p) (cyclotomicKernelGenerator p)} := by
  rw [DeRham.deRhamIdeal, DeRhamEmbedding.bInfTheta_kernel_eq_map, theta_kernel_cyclotomic_generator,
    Ideal.map_span, Set.image_singleton]

def cyclotomicRootDifference : DeRhamDVR.DeRhamCompletion p :=
  DeRhamEmbedding.aInfToBdRPlus p (WittVector.teichmuller p (epsilonRoot p) - 1)

theorem cyclotomicRootDifference_isUnit : IsUnit (cyclotomicRootDifference p) := by
  apply DeRhamDVR.residue_ne_zero_isUnit p
  change DeRham.integerLocalizationToCp p
    (DeRham.thetaBdRPlus p (DeRham.bInfToBdRPlus p (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p)
      (WittVector.teichmuller p (epsilonRoot p) - 1)))) ≠ 0
  rw [DeRham.thetaBdRPlus_aInf, DeRham.integerLocalizationToCp_algebraMap]
  change ((Logarithm.PeriodRings.theta p (WittVector.teichmuller p (epsilonRoot p) - 1) : 𝓞_ℂ_[p]) : ℂ_[p]) ≠ 0
  rw [map_sub, map_one, theta_epsilonRoot_teich]
  change Logarithm.PeriodRings.firstCyclotomicRoot p - 1 ≠ 0
  exact sub_ne_zero.mpr ((Logarithm.PeriodRings.firstCyclotomicRoot_primitive p).ne_one (Fact.out : p.Prime).one_lt)

theorem associated_xi_cyclotomicGenerator : Associated (DeRhamDVR.xiDeRham p)
    (DeRhamEmbedding.aInfToBdRPlus p (cyclotomicKernelGenerator p) : DeRhamDVR.DeRhamCompletion p) := by
  apply Ideal.span_singleton_eq_span_singleton.mp
  rw [← DeRhamDVR.residue_kernel_span, DeRhamDVR.residue_kernel]
  have he := congrArg (Ideal.map (algebraMap (Logarithm.PeriodRings.BInf p) (DeRhamDVR.DeRhamCompletion p)))
    (deRhamIdeal_cyclotomic_generator p)
  rw [Ideal.map_span, Set.image_singleton] at he
  exact he

theorem associated_xi_cyclotomicDifference : Associated (DeRhamDVR.xiDeRham p)
    (DeRhamEmbedding.aInfToBdRPlus p (Logarithm.PeriodRings.cyclotomicDifference p) : DeRhamDVR.DeRhamCompletion p) := by
  apply (associated_xi_cyclotomicGenerator p).trans
  refine ⟨(cyclotomicRootDifference_isUnit p).unit, ?_⟩
  rw [(cyclotomicRootDifference_isUnit p).unit_spec]
  change DeRhamEmbedding.aInfToBdRPlus p (cyclotomicKernelGenerator p) *
    DeRhamEmbedding.aInfToBdRPlus p (WittVector.teichmuller p (epsilonRoot p) - 1) =
      DeRhamEmbedding.aInfToBdRPlus p (Logarithm.PeriodRings.cyclotomicDifference p)
  rw [← map_mul, ← cyclotomicDifference_factor]

/-- The cyclotomic period is a uniformizer of the actual de Rham completion. -/
theorem associated_xi_cyclotomicPeriod : Associated (DeRhamDVR.xiDeRham p)
    (Comparison.aCrisToBdRPlus p (Logarithm.PeriodRings.cyclotomicPeriod p) : DeRhamDVR.DeRhamCompletion p) := by
  apply (associated_xi_cyclotomicDifference p).trans
  refine ⟨(DeRhamLog.logFactor_isUnit p (Logarithm.PeriodRings.cyclotomicDifference p) (Logarithm.PeriodRings.cyclotomicDifference_theta p)).unit, ?_⟩
  rw [(DeRhamLog.logFactor_isUnit p (Logarithm.PeriodRings.cyclotomicDifference p) (Logarithm.PeriodRings.cyclotomicDifference_theta p)).unit_spec]
  exact (DeRhamLog.aCrisToBdRPlus_log p _ (Logarithm.PeriodRings.cyclotomicDifference_theta p) (Logarithm.PeriodRings.cyclotomicDifference_thetaModP p)).symm

theorem cyclotomicPeriod_generates_filtration :
    RingHom.ker (DeRhamDVR.residue p) = Ideal.span {(Comparison.aCrisToBdRPlus p (Logarithm.PeriodRings.cyclotomicPeriod p) : DeRhamDVR.DeRhamCompletion p)} := by
  rw [DeRhamDVR.residue_kernel_span]
  exact Ideal.span_singleton_eq_span_singleton.mpr (associated_xi_cyclotomicPeriod p)

theorem cyclotomicPeriod_irreducible :
    Irreducible (Comparison.aCrisToBdRPlus p (Logarithm.PeriodRings.cyclotomicPeriod p) : DeRhamDVR.DeRhamCompletion p) :=
  (associated_xi_cyclotomicPeriod p).irreducible
    (IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
      (DeRhamDVR.xiDeRham_ne_zero p) (DeRhamDVR.maximalIdeal_span p))

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.PeriodUniformizer
