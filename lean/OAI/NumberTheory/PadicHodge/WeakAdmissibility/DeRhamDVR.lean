import OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEmbedding
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.PrincipalCompletion

/-! # De Rham DVR -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamDVR

noncomputable section

/-! The actual de Rham completion is a discrete valuation ring. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaKernel OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRham OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEmbedding OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEmbedding.Residue
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.PrincipalCompletion
variable (p : ℕ) [Fact p.Prime]

abbrev DeRhamCompletion := AdicCompletion (DeRham.deRhamIdeal p) (Logarithm.PeriodRings.BInf p)

instance bInf_domain : IsDomain (Logarithm.PeriodRings.BInf p) :=
  (PeriodInvariants.Nontriviality.binfToFraction_injective p).isDomain (PeriodInvariants.Nontriviality.binfToFraction p)

def xiDeRham : DeRhamCompletion p := algebraMap (Logarithm.PeriodRings.BInf p) (DeRhamCompletion p) (DeRhamEmbedding.xiBInf p)

def residue : DeRhamCompletion p →+* ℂ_[p] := DeRham.thetaBdRPlusCp p

theorem residue_of (a : Logarithm.PeriodRings.BInf p) :
    residue p (algebraMap (Logarithm.PeriodRings.BInf p) (DeRhamCompletion p) a) =
      DeRham.integerLocalizationToCp p (DeRham.bInfTheta p a) := by
  change DeRham.integerLocalizationToCp p (DeRham.thetaBdRPlus p (DeRham.bInfToBdRPlus p a)) = _
  rw [DeRham.thetaBdRPlus_bInf]

theorem residue_surjective : Function.Surjective (residue p) := by
  intro z
  obtain ⟨a, ha⟩ := DeRhamEmbedding.Residue.bInfThetaCp_surjective p z
  exact ⟨algebraMap (Logarithm.PeriodRings.BInf p) (DeRhamCompletion p) a, (residue_of p a).trans ha⟩

theorem thetaReduction_injective : Function.Injective (DeRham.thetaReduction p) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change DeRham.bInfTheta p a = 0 at hz
  simpa only [pow_one, RingHom.mem_ker] using hz

theorem residue_kernel : RingHom.ker (residue p) =
    (DeRham.deRhamIdeal p).map (algebraMap (Logarithm.PeriodRings.BInf p) (DeRhamCompletion p)) := by
  apply Eq.trans (b := RingHom.ker (AdicCompletion.evalOneₐ (DeRham.deRhamIdeal p)).toRingHom)
    ?_ (AdicCompletion.ker_evalOneₐ_eq_map (DeRham.deRhamIdeal p) (DeRhamEmbedding.deRhamIdeal_fg p))
  ext x
  change DeRham.integerLocalizationToCp p
    (DeRham.thetaReduction p (AdicCompletion.evalₐ (DeRham.deRhamIdeal p) 1 x)) = 0 ↔
      AdicCompletion.evalOneₐ (DeRham.deRhamIdeal p) x = 0
  rw [map_eq_zero_iff _ (DeRhamEmbedding.Residue.integerLocalizationToCp_injective p),
    map_eq_zero_iff _ (thetaReduction_injective p)]
  rw [← AdicCompletion.factorₐ_evalₐ_one]
  constructor
  · intro h; rw [h, map_zero]
  · intro h
    have hinj : Function.Injective
        (Ideal.Quotient.factor (show (DeRham.deRhamIdeal p) ^ 1 ≤ DeRham.deRhamIdeal p by simp)) := by
      apply (injective_iff_map_eq_zero _).mpr
      intro z hz
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      simpa only [pow_one] using Ideal.Quotient.eq_zero_iff_mem.mp hz
    exact (map_eq_zero_iff _ hinj).mp h

theorem residue_kernel_span : RingHom.ker (residue p) = Ideal.span {xiDeRham p} := by
  rw [residue_kernel]
  have he := congrArg (Ideal.map (algebraMap (Logarithm.PeriodRings.BInf p) (DeRhamCompletion p)))
    (DeRhamEmbedding.deRhamIdeal_eq_span p)
  rw [Ideal.map_span, Set.image_singleton] at he
  exact he

instance completion_complete : IsAdicComplete (Ideal.span {xiDeRham p}) (DeRhamCompletion p) := by
  have hc : IsAdicComplete (DeRham.deRhamIdeal p) (DeRhamCompletion p) :=
    AdicCompletion.isAdicComplete (DeRhamEmbedding.deRhamIdeal_fg p)
  have hm := (IsAdicComplete.map_algebraMap_iff (S := DeRhamCompletion p)
    (DeRham.deRhamIdeal p) (DeRhamCompletion p)).mpr hc
  rw [← residue_kernel, residue_kernel_span] at hm
  exact hm

theorem residue_kernel_jacobson : RingHom.ker (residue p) ≤ (⊥ : Ideal (DeRhamCompletion p)).jacobson := by
  rw [residue_kernel_span]
  exact IsAdicComplete.le_jacobson_bot (I := Ideal.span {xiDeRham p})

theorem residue_ne_zero_isUnit (x : DeRhamCompletion p) (hx : residue p x ≠ 0) : IsUnit x :=
  PrincipalCompletion.isUnit_of_residue_ne_zero (residue p) (residue_surjective p) (residue_kernel_jacobson p) x hx

theorem xiDeRham_ne_zero : xiDeRham p ≠ 0 := DeRhamEmbedding.thetaGenerator_deRham_ne_zero p

theorem xiDeRham_cancel (x : DeRhamCompletion p) (hx : xiDeRham p * x = 0) : x = 0 :=
  PrincipalCompletion.completion_generator_cancel (DeRham.deRhamIdeal p) (DeRhamEmbedding.xiBInf p) (DeRhamEmbedding.deRhamIdeal_eq_span p)
    (by
      intro h
      apply ThetaKernel.thetaGenerator_ne_zero p
      apply PeriodInvariants.Nontriviality.binf_algebraMap_injective p
      exact h.trans (map_zero _).symm) x hx

theorem xiDeRham_pow_cancel (n : ℕ) (x : DeRhamCompletion p)
    (hx : xiDeRham p ^ n * x = 0) : x = 0 := by
  induction n with
  | zero => simpa only [pow_zero, one_mul] using hx
  | succ n ih =>
    apply ih
    apply xiDeRham_cancel p
    rw [← mul_assoc, ← pow_succ', hx]

theorem exists_unit_factor (x : DeRhamCompletion p) (hx : x ≠ 0) :
    ∃ n : ℕ, ∃ u : (DeRhamCompletion p)ˣ, x = xiDeRham p ^ n * u := by
  obtain ⟨n, a, ha, hqa⟩ := PrincipalCompletion.exists_order_factor (xiDeRham p) x hx
  have hθ : residue p a ≠ 0 := by
    intro hz
    apply hqa
    apply Ideal.mem_span_singleton.mp
    rw [← residue_kernel_span, RingHom.mem_ker]
    exact hz
  obtain ⟨u, hu⟩ := residue_ne_zero_isUnit p a hθ
  exact ⟨n, u, ha.trans (congrArg (xiDeRham p ^ n * ·) hu.symm)⟩

instance completion_noZeroDivisors : NoZeroDivisors (DeRhamCompletion p) where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} h := by
    by_cases hx : x = 0
    · exact Or.inl hx
    · right
      obtain ⟨n, u, hu⟩ := exists_unit_factor p x hx
      rw [hu, mul_assoc] at h
      exact u.isUnit.mul_left_cancel ((xiDeRham_pow_cancel p n _ h).trans (mul_zero _).symm)

instance completion_nontrivial : Nontrivial (DeRhamCompletion p) :=
  (residue p).domain_nontrivial

instance completion_domain : IsDomain (DeRhamCompletion p) := NoZeroDivisors.to_isDomain _

instance completion_localRing : IsLocalRing (DeRhamCompletion p) := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro x
  by_cases hx : residue p x = 0
  · right
    apply residue_ne_zero_isUnit p
    rw [map_sub, map_one, hx, sub_zero]
    exact one_ne_zero
  · exact Or.inl (residue_ne_zero_isUnit p x hx)

theorem xiDeRham_not_isUnit : ¬IsUnit (xiDeRham p) := by
  intro h
  have hz : residue p (xiDeRham p) = 0 := by
    apply RingHom.mem_ker.mp
    rw [residue_kernel_span]
    exact Ideal.subset_span (Set.mem_singleton _)
  exact (h.map (residue p)).ne_zero hz

theorem maximalIdeal_span : IsLocalRing.maximalIdeal (DeRhamCompletion p) = Ideal.span {xiDeRham p} := by
  ext x
  change ¬IsUnit x ↔ x ∈ Ideal.span {xiDeRham p}
  rw [← residue_kernel_span, RingHom.mem_ker]
  constructor
  · intro h
    by_contra hx
    exact h (residue_ne_zero_isUnit p x hx)
  · intro h hu
    exact (hu.map (residue p)).ne_zero h

instance completion_discreteValuationRing : IsDiscreteValuationRing (DeRhamCompletion p) := by
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨xiDeRham p, IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
    (xiDeRham_ne_zero p) (maximalIdeal_span p), ?_⟩
  intro x hx
  obtain ⟨n, u, hu⟩ := exists_unit_factor p x hx
  exact ⟨n, u, hu.symm⟩

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamDVR
