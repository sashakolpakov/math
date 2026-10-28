import OAI.NumberTheory.PadicHodge.PeriodInvariants.PrincipalAdicLinearCriterion
import OAI.NumberTheory.PadicHodge.PeriodInvariants.WittAlgebraCompleteness
import OAI.NumberTheory.PadicHodge.PeriodInvariants.WittCoefficientRegularity
import OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicFiniteModules

/-! # Witt Finite Basis -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.WittFiniteBasis

noncomputable section

/-! # A finite basis of perfect characteristic-p algebras lifts to a Witt-vector basis -/

attribute [local instance] WittAlgebraFunctor.wittAlgebra

variable (p : ℕ) [Fact p.Prime] {A B ι : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [CharP A p] [PerfectRing A p] [CharP B p] [PerfectRing B p] [Fintype ι]
  (b : Module.Basis ι A B)

def lift : (ι → WittVector p A) →ₗ[WittVector p A] WittVector p B :=
  Fintype.linearCombination (WittVector p A) (fun i => WittVector.teichmuller p (b i))

omit [CharP A p] [PerfectRing A p] [CharP B p] [PerfectRing B p] in
theorem coefficient (c : ι → WittVector p A) :
    (lift p b c).coeff 0 = b.equivFun.symm (fun i => (c i).coeff 0) := by
  rw [Module.Basis.equivFun_symm_apply]
  change WittVector.constantCoeff (∑ i, c i • WittVector.teichmuller p (b i)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change WittVector.constantCoeff (WittVector.map (algebraMap A B) (c i) *
    WittVector.teichmuller p (b i)) = _
  rw [map_mul]
  change algebraMap A B ((c i).coeff 0) * b i = (c i).coeff 0 • b i
  rw [Algebra.smul_def]

theorem reflects (c : ι → WittVector p A)
    (hc : ∃ y, (p : WittVector p A) • y = lift p b c) :
    ∃ y, (p : WittVector p A) • y = c := by
  obtain ⟨y, hy⟩ := hc
  have hd : (p : WittVector p B) ∣ lift p b c := by
    refine ⟨y, ?_⟩
    simpa only [Algebra.smul_def, map_natCast] using hy.symm
  have hz := (WittVector.mem_span_p_iff_coeff_zero_eq_zero (lift p b c)).mp
    (Ideal.mem_span_singleton.mpr hd)
  rw [coefficient] at hz
  have he : (fun i => (c i).coeff 0) = (0 : ι → A) :=
    b.equivFun.symm.injective (hz.trans (map_zero _).symm)
  have hdiv (i : ι) : (p : WittVector p A) ∣ c i :=
    Ideal.mem_span_singleton.mp ((WittVector.mem_span_p_iff_coeff_zero_eq_zero (c i)).mpr (congrFun he i))
  choose z hz using hdiv
  exact ⟨z, funext fun i => (hz i).symm⟩

theorem injective : Function.Injective (lift p b) := by
  classical
  have : IsAdicComplete (Ideal.span {(p : WittVector p A)}) (ι → WittVector p A) :=
    AdicFiniteModules.pi_complete _
  have hp : IsSMulRegular (WittVector p B) (p : WittVector p A) := by
    apply (isSMulRegular_algebraMap_iff (WittVector p B)).mp
    simpa only [map_natCast] using WittCoefficientRegularity.p_regular p (R := B)
  exact PrincipalAdicLinearCriterion.injective (p : WittVector p A) (lift p b) hp (reflects p b)

omit [CharP A p] [PerfectRing A p] in
theorem residue_surjective : Function.Surjective
    ((Submodule.mkQ (Ideal.span {(p : WittVector p A)} • (⊤ : Submodule (WittVector p A) (WittVector p B)))).comp
      (lift p b)) := by
  intro x
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ x
  let c : ι → WittVector p A := fun i => WittVector.teichmuller p (b.equivFun (w.coeff 0) i)
  refine ⟨c, ?_⟩
  change Submodule.Quotient.mk (lift p b c) = Submodule.Quotient.mk w
  rw [Submodule.Quotient.eq]
  have hz : (lift p b c - w).coeff 0 = 0 := by
    change WittVector.constantCoeff (lift p b c - w) = 0
    rw [map_sub]
    change (lift p b c).coeff 0 - w.coeff 0 = 0
    rw [coefficient]
    change b.equivFun.symm (b.equivFun (w.coeff 0)) - w.coeff 0 = 0
    rw [LinearEquiv.symm_apply_apply, sub_self]
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp
    ((WittVector.mem_span_p_iff_coeff_zero_eq_zero (lift p b c - w)).mpr hz)
  have hs : (p : WittVector p A) • z = lift p b c - w := by
    simpa only [Algebra.smul_def, map_natCast] using hz.symm
  simpa only [pow_one] using
    (ScalarDivisibilityModules.principal_power_mem (p : WittVector p A) 1 _).mpr
      ⟨z, by simpa only [pow_one] using hs⟩

theorem surjective : Function.Surjective (lift p b) := by
  classical
  have : IsAdicComplete (Ideal.span {(p : WittVector p A)}) (ι → WittVector p A) :=
    AdicFiniteModules.pi_complete _
  have : IsAdicComplete (Ideal.span {(p : WittVector p A)}) (WittVector p B) :=
    WittAlgebraCompleteness.complete p A B
  exact surjective_of_mkQ_comp_surjective (residue_surjective p b)

def equiv : (ι → WittVector p A) ≃ₗ[WittVector p A] WittVector p B :=
  LinearEquiv.ofBijective (lift p b) ⟨WittFiniteBasis.injective p b, surjective p b⟩

def basis : Module.Basis ι (WittVector p A) (WittVector p B) := Module.Basis.ofEquivFun (equiv p b).symm

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.WittFiniteBasis
