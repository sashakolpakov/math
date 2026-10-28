import OAI.RepresentationTheory.Weil.AdelicSplitting.FinitePositionInsert
import OAI.RepresentationTheory.Weil.AdelicSplitting.LocalCompact

/-! # Finite Test Support -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting

noncomputable section

/-! The finite function of a restricted Bruhat family has compact support.
A single nonzero algebraic integer clears all exceptional local supports. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.finiteValue_denominator (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    ∃ r : 𝓞 F, r ≠ 0 ∧ ∀ a : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F, f.finiteValue F N a ≠ 0 →
      ∀ i, algebraMap (𝓞 F) (ArchimedeanAdeles.Construction.FiniteAdeles F) r * a i ∈ IntegralAdeles.Construction.finiteIntegralRing F := by
  have hlocal (v : HeightOneSpectrum (𝓞 F)) :
      IsCompact (tsupport (f (.inr v)).val) :=
    (NonarchimedeanIntertwiner.LocalAnalysis.schwartzBruhat_totallyDisconnected_iff.mp (f (.inr v)).property).2
  choose d hd hb using fun v => LocalCompact.Construction.compact_local_integer_denominator F v N _ (hlocal v)
  have hs := eventually_cofinite.mp f.unramified
  let s := hs.toFinset
  let r : 𝓞 F := ∏ v ∈ s, d v
  refine ⟨r, Finset.prod_ne_zero_iff.mpr (fun v _ => hd v), fun a ha i v => ?_⟩
  have hnz (w : HeightOneSpectrum (𝓞 F)) : (f (.inr w)).val (fun j => a j w) ≠ 0 := by
    intro hw
    exact ha (tprod_of_exists_eq_zero ⟨w, hw⟩)
  change algebraMap (𝓞 F) (v.adicCompletion F) r * a i v ∈ v.adicCompletionIntegers F
  by_cases hv : v ∈ s
  · have hbound := hb v (subset_tsupport _ (hnz v))
    have hdv : d v ∣ r := Finset.dvd_prod_of_mem d hv
    exact LocalCompact.Construction.localIntegerPositionBox_mono F v N hdv hbound i
  · have hf : f (.inr v) = Vacuum.Construction.finiteVacuum F N v := by simpa [s] using hv
    have hint : ∀ j, a j v ∈ v.adicCompletionIntegers F := by
      by_contra hh
      apply hnz v
      rw [hf]
      exact FinitePositionInsert.Construction.finiteVacuum_eq_zero_of_not_integral F N v _ hh
    exact (v.adicCompletionIntegers F).toSubring.mul_mem
      (coe_mem_adicCompletionIntegers (K := F) v r) (hint i)

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.finiteValue_compactSupport (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    HasCompactSupport (f.finiteValue F N) := by
  obtain ⟨r, hr, hb⟩ := f.finiteValue_denominator F N
  let q := algebraMap (𝓞 F) F r
  have hq : q ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hr
  apply HasCompactSupport.intro (FiniteLattices.Construction.finiteAdelicPositionLattice_isCompact q⁻¹ (inv_ne_zero hq))
  intro a ha
  by_contra hnz
  apply ha
  apply (FiniteLattices.Construction.finiteAdelicPositionLattice_mem_iff q⁻¹ (inv_ne_zero hq) a).mpr
  intro i
  have hh := hb a hnz i
  change algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) (q⁻¹)⁻¹ * a i ∈ IntegralAdeles.Construction.finiteIntegralRing F
  rw [inv_inv]
  simpa only [q, IsScalarTower.algebraMap_apply] using! hh

end

end OAI.RepresentationTheory.Weil.AdelicSplitting
