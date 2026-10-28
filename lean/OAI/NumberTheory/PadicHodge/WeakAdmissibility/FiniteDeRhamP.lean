import OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEmbedding

/-! # Finite De Rham P -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.FiniteDeRhamP

noncomputable section

/-! Integral lattices in the finite quotients of the actual de Rham ring. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaKernel OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaQuotients OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRham OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEmbedding
variable (p : ℕ) [Fact p.Prime]

abbrev FiniteDeRham (m : ℕ) := Logarithm.PeriodRings.BInf p ⧸ (DeRham.deRhamIdeal p) ^ m

def integralToFinite (m : ℕ) : ThetaQuotients.ThetaPowerQuotient p m →+* FiniteDeRham p m :=
  Ideal.quotientMap _ (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p)) (by
    rw [← Ideal.map_le_iff_le_comap, ← DeRhamEmbedding.deRhamIdeal_power_eq_map])

theorem integralToFinite_mk (m : ℕ) (a : Logarithm.PeriodRings.AInf p) :
    integralToFinite p m (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p) a) := rfl

theorem integralToFinite_injective (m : ℕ) : Function.Injective (integralToFinite p m) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hz
  change algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p) a ∈ (DeRham.deRhamIdeal p) ^ m at hmem
  rw [DeRhamEmbedding.deRhamIdeal_power_eq_map] at hmem
  obtain ⟨t, ht, hta⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers (p : Logarithm.PeriodRings.AInf p))
      (Logarithm.PeriodRings.BInf p) (Ideal.span {ThetaKernel.thetaGenerator p ^ m}) a).mp hmem
  obtain ⟨n, rfl⟩ := ht
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (ThetaQuotients.thetaPower_p_saturated p m n a hta)

def uncompletedToFinite (m : ℕ) : Logarithm.PeriodRings.ACrisUncompleted p →+* FiniteDeRham p m :=
  (Ideal.Quotient.mk _).comp (DeRhamEnvelope.uncompletedToBInf p)

theorem uncompletedToFinite_algebraMap (m : ℕ) (a : Logarithm.PeriodRings.AInf p) :
    uncompletedToFinite p m (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) a) =
      integralToFinite p m (Ideal.Quotient.mk _ a) := by
  simp only [uncompletedToFinite, RingHom.comp_apply,
    DeRhamEnvelope.uncompletedToBInf_algebraMap, integralToFinite_mk]

def padicToFinite (m : ℕ) : ℚ_[p] →+* FiniteDeRham p m :=
  (Ideal.Quotient.mk _).comp (PeriodInvariants.Nontriviality.padicToBinf p)

theorem factorial_isUnit (m n : ℕ) : IsUnit (n.factorial : FiniteDeRham p m) := by
  have h : IsUnit (n.factorial : ℚ_[p]) :=
    isUnit_iff_ne_zero.mpr (by exact_mod_cast Nat.factorial_ne_zero n)
  simpa only [map_natCast] using h.map (padicToFinite p m)

theorem p_isUnit (m : ℕ) : IsUnit (p : FiniteDeRham p m) := by
  have h : IsUnit (p : ℚ_[p]) :=
    isUnit_iff_ne_zero.mpr (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  simpa only [map_natCast] using h.map (padicToFinite p m)

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.FiniteDeRhamP
