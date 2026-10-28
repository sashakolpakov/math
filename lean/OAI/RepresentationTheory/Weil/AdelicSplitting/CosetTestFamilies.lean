import OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteLatticeFactors
import OAI.RepresentationTheory.Weil.AdelicSplitting.FinitePositionInsert

/-! # Coset Test Families -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting

noncomputable section

/-! Compact open finite-adelic cosets give actual restricted Bruhat
families with the prescribed vacuum tail. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Filter

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

theorem CosetTestFamilies.Construction.finiteLocalScalarLattice_eq_integral (q : F) (hq : q ≠ 0) (v : HeightOneSpectrum (𝓞 F))
    (hv : ArchimedeanAdeles.Construction.rationalScalar F (.inr v) q ∈ v.adicCompletionIntegers F)
    (hi : ArchimedeanAdeles.Construction.rationalScalar F (.inr v) q⁻¹ ∈ v.adicCompletionIntegers F) :
    FiniteLatticeFactors.Construction.finiteLocalScalarLattice F N q hq v = FiniteLatticeFactors.Construction.finiteLocalIntegralPositions F N v := by
  have hqv : ArchimedeanAdeles.Construction.rationalScalar F (.inr v) q ≠ 0 := by
    exact_mod_cast (map_ne_zero_iff _ (ArchimedeanAdeles.Construction.rationalScalar F (.inr v)).injective).mpr hq
  ext x
  rw [FiniteLatticeFactors.Construction.finiteLocalScalarLattice_mem_iff]
  constructor
  · intro hx i
    have h := (v.adicCompletionIntegers F).toSubring.mul_mem hv (hx i)
    simpa only [← mul_assoc, mul_inv_cancel₀ hqv, one_mul] using! h
  · intro hx i
    have h := (v.adicCompletionIntegers F).toSubring.mul_mem hi (hx i)
    simpa only [map_inv₀] using! h

def CosetTestFamilies.Construction.finiteCosetTest (q : F) (hq : q ≠ 0) (a : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F) (v : HeightOneSpectrum (𝓞 F)) :
    Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F (.inr v)) N :=
  ⟨LocalCosetFourier.Analysis.localCosetIndicator (FiniteLatticeFactors.Construction.finiteLocalScalarLattice F N q hq v) (fun i => a i v),
    LocalCosetFourier.Analysis.localCosetIndicator_mem _ (FiniteLatticeFactors.Construction.finiteLocalScalarLattice_compact F N q hq v) _⟩

theorem CosetTestFamilies.Construction.finiteCosetTest_eq_vacuum (q : F) (hq : q ≠ 0) (a : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F)
    (v : HeightOneSpectrum (𝓞 F))
    (hv : ArchimedeanAdeles.Construction.rationalScalar F (.inr v) q ∈ v.adicCompletionIntegers F)
    (hi : ArchimedeanAdeles.Construction.rationalScalar F (.inr v) q⁻¹ ∈ v.adicCompletionIntegers F)
    (ha : ∀ i, a i v ∈ v.adicCompletionIntegers F) :
    CosetTestFamilies.Construction.finiteCosetTest F N q hq a v = Vacuum.Construction.finiteVacuum F N v := by
  apply Subtype.ext
  funext x
  change LocalCosetFourier.Analysis.localCosetIndicator (FiniteLatticeFactors.Construction.finiteLocalScalarLattice F N q hq v) (fun i => a i v) x = _
  rw [CosetTestFamilies.Construction.finiteLocalScalarLattice_eq_integral F N q hq v hv hi]
  have haU : (fun i => a i v) ∈ FiniteLatticeFactors.Construction.finiteLocalIntegralPositions F N v := ha
  have hm : x - (fun i => a i v) ∈ FiniteLatticeFactors.Construction.finiteLocalIntegralPositions F N v ↔
      x ∈ FiniteLatticeFactors.Construction.finiteLocalIntegralPositions F N v :=
    by
      constructor
      · intro h
        simpa only [sub_add_cancel] using! (FiniteLatticeFactors.Construction.finiteLocalIntegralPositions F N v).add_mem h haU
      · intro h
        exact (FiniteLatticeFactors.Construction.finiteLocalIntegralPositions F N v).sub_mem h haU
  by_cases hx : x ∈ FiniteLatticeFactors.Construction.finiteLocalIntegralPositions F N v
  · rw [LocalCosetFourier.Analysis.localCosetIndicator, Set.indicator_of_mem (hm.mpr hx)]
    exact (RestrictedTestFamilies.Construction.finiteVacuum_eq_one_of_integral F N v x hx).symm
  · rw [LocalCosetFourier.Analysis.localCosetIndicator, Set.indicator_of_notMem (fun h => hx (hm.mp h))]
    exact (FinitePositionInsert.Construction.finiteVacuum_eq_zero_of_not_integral F N v x hx).symm

theorem CosetTestFamilies.Construction.finiteCosetTest_eventually_vacuum (q : F) (hq : q ≠ 0) (a : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      CosetTestFamilies.Construction.finiteCosetTest F N q hq a v = Vacuum.Construction.finiteVacuum F N v := by
  have hqf := Sum.inr_injective.tendsto_cofinite.eventually (Integral.Construction.rationalScalar_integral F q)
  have hif := Sum.inr_injective.tendsto_cofinite.eventually (Integral.Construction.rationalScalar_integral F q⁻¹)
  have haf : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ∀ i, a i v ∈ v.adicCompletionIntegers F := eventually_all.mpr (fun i => (a i).property)
  filter_upwards [hqf, hif, haf] with v hv hi ha
  exact CosetTestFamilies.Construction.finiteCosetTest_eq_vacuum F N q hq a v hv hi ha

def RestrictedTestFamilies.Construction.RestrictedTestFamily.replaceFiniteByCoset (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N)
    (q : F) (hq : q ≠ 0) (a : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F) : RestrictedTestFamilies.Construction.RestrictedTestFamily F N where
  component v := match v with
    | .inl v => f (.inl v)
    | .inr v => CosetTestFamilies.Construction.finiteCosetTest F N q hq a v
  unramified := CosetTestFamilies.Construction.finiteCosetTest_eventually_vacuum F N q hq a

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.replaceFiniteByCoset_finiteValue (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N)
    (q : F) (hq : q ≠ 0) (a x : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F) :
    (f.replaceFiniteByCoset F N q hq a).finiteValue F N x = FiniteCosets.Construction.finitePositionCosetIndicator q hq a x :=
  (FiniteLatticeFactors.Construction.finitePositionCosetIndicator_product F N q hq a x).symm

end

end OAI.RepresentationTheory.Weil.AdelicSplitting
