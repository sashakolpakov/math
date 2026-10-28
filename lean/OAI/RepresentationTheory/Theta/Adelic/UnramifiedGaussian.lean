import OAI.RepresentationTheory.Weil.Local.GeneralGaussianCutoff
import OAI.RepresentationTheory.Weil.UnitarySplitting.DiagonalNormGaussian

/-! # Unramified Gaussian -/

namespace OAI.RepresentationTheory.Theta.Adelic.UnramifiedGaussian

noncomputable section

/-! Unit-coefficient Gaussian phases are one on a self-annihilating
integer lattice with trivial quadratic phase. This is uniform in the unit. -/

open scoped Classical

open Set _root_.MeasureTheory
open OAI.RepresentationTheory.Weil.Local.GeneralGaussianCutoff.Construction OAI.RepresentationTheory.Weil.UnitarySplitting.DiagonalNormGaussian.Construction

theorem gaussianIndex_eq_one_of_selfDual_domain
    {k : Type} [NormedField k] [LocallyCompactSpace k] [IsUltrametricDist k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ)
    (hc : Continuous (fun x : k => ψ x)) (hu : ∀ x : k, ‖ψ x‖ = 1)
    (hn : ∃ x : k, ψ x ≠ 1) (a : kˣ) (U : OpenAddSubgroup k)
    (hU : IsCompact (U : Set k))
    (hphase : ∀ t ∈ U, ψ (a.val * t ^ 2 / 2) = 1)
    (hdual : ∀ y, y ∈ U ↔ a.val * y ∈ Weil.Local.QuadraticFourier.Construction.scalarAnnihilator ψ U.toAddSubgroup) :
    Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val = 1 := by
  let : SecondCountableTopology k := Weil.Local.FunctionsMetaplectic.Construction.localField_secondCountable k hnd
  let μ := Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ
  let : μ.IsAddHaarMeasure := Weil.Local.NonarchimedeanHaar.Construction.nonarchimedean_selfDualMeasure_isAddHaarMeasure hnd ψ hu hc hn
  obtain ⟨W, hW, hUW, hGW⟩ := Weil.Local.GeneralGaussianCutoff.Construction.exists_gaussian_coefficient_cutoff hnd ψ hu hc hn a U hU
  have hstable := Weil.Local.GaussianCompact.Construction.compactGaussian_stabilizes_of_annihilator ψ hc μ a.val U U W hU hW
    le_rfl hUW hphase hdual
  have hVol : (∫ x in (U : Set k), ψ (a.val * x ^ 2 / 2) ∂μ) = (μ.real (U : Set k) : ℂ) := by
    have he : (U : Set k).indicator (fun x => ψ (a.val * x ^ 2 / 2)) =
        (U : Set k).indicator (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : x ∈ U
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hphase x hx]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    rw [← integral_indicator U.isOpen.measurableSet, he,
      integral_indicator_const _ U.isOpen.measurableSet, Complex.real_smul, mul_one]
  have he := hGW.symm.trans (hstable.trans hVol)
  have hp := congrArg Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase he
  rw [Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase_mul, ← Complex.ofReal_inv,
    Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase_positive _ (inv_pos.mpr (Real.sqrt_pos.mpr (Weil.Local.FunctionsMetaplectic.Construction.localModulus_pos k a))),
    Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase_positive _ (Weil.Local.NonarchimedeanFourier.Construction.compact_open_subgroup_real_pos μ U hU), mul_one] at hp
  change Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val / (‖Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val‖ : ℂ) = 1 at hp
  rw [Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex_norm k ψ a.val
    (Weil.Local.GaussianCompact.Construction.nonarchimedean_gaussian_limit_nonzero hnd ψ hu hc hn a.val a.ne_zero).2,
    Complex.ofReal_one, div_one] at hp
  exact hp

theorem gaussianIndex_integral_unit
    {k : Type} [NormedField k] [LocallyCompactSpace k] [IsUltrametricDist k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ)
    (hc : Continuous (fun x : k => ψ x)) (hu : ∀ x : k, ‖ψ x‖ = 1)
    (hn : ∃ x : k, ψ x ≠ 1) (S : Subring k)
    (hSo : IsOpen (S : Set k)) (hSc : IsCompact (S : Set k))
    (hψ : ∀ x ∈ S, ψ x = 1)
    (hAnn : ∀ u, (∀ t ∈ S, ψ (u * t) = 1) → u ∈ S)
    (hhalf : (2 : k)⁻¹ ∈ S) (a : kˣ) (ha : a.val ∈ S) (hai : a.val⁻¹ ∈ S) :
    Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val = 1 := by
  let U : OpenAddSubgroup k := ⟨S.toAddSubgroup, hSo⟩
  apply gaussianIndex_eq_one_of_selfDual_domain hnd ψ hc hu hn a U hSc
  · intro t ht
    apply hψ
    rw [div_eq_mul_inv]
    exact S.mul_mem (S.mul_mem ha (S.pow_mem ht 2)) hhalf
  · intro y
    change y ∈ S ↔ ∀ t ∈ S, ψ ((a.val * y) * t) = 1
    constructor
    · intro hy t ht
      exact hψ _ (S.mul_mem (S.mul_mem ha hy) ht)
    · intro hy
      have hay := hAnn (a.val * y) hy
      have hh := S.mul_mem hai hay
      simpa only [inv_mul_cancel_left₀ a.ne_zero] using hh

end

end OAI.RepresentationTheory.Theta.Adelic.UnramifiedGaussian
