import OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalGaussian
import OAI.RepresentationTheory.Theta.Adelic.UnramifiedGaussian

/-! # Unramified Norm Character -/

namespace OAI.RepresentationTheory.Theta.Adelic.UnramifiedNormCharacter

noncomputable section

/-! The actual quadratic norm character is trivial on integral units at
unramified places, uniformly in the unit rather than pointwise in F. -/

open Set
open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalGaussian OAI.RepresentationTheory.Theta.Adelic.UnramifiedGaussian

theorem normSign_integral_unit
    {k : Type} [NontriviallyNormedField k] [CompleteSpace k] [LocallyCompactSpace k]
    [IsUltrametricDist k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
    (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ)
    (hc : Continuous (fun x : k => ψ x)) (hu : ∀ x : k, ‖ψ x‖ = 1)
    (hn : ∃ x : k, ψ x ≠ 1) (S : Subring k)
    (hSo : IsOpen (S : Set k)) (hSc : IsCompact (S : Set k))
    (hψ : ∀ x ∈ S, ψ x = 1)
    (hAnn : ∀ u, (∀ t ∈ S, ψ (u * t) = 1) → u ∈ S)
    (hhalf : (2 : k)⁻¹ ∈ S) (d : k) (hd : d ≠ 0) (hdS : d ∈ S) (hdiS : d⁻¹ ∈ S)
    (a : kˣ) (ha : a.val ∈ S) (hai : a.val⁻¹ ∈ S) : QuadraticNormCharacter.normSign d a = 1 := by
  by_cases hsq : IsSquare d
  · exact QuadraticNormCharacter.normSign_split d hd hsq a
  · let U := S.toSubmonoid.units
    let t : kˣ := Units.mk0 2 (by norm_num)
    let D : kˣ := Units.mk0 d hd
    have ht : t ∈ U := (Submonoid.mem_units_iff S.toSubmonoid t).mpr
      ⟨by change (2 : k) ∈ S
          simpa only [one_add_one_eq_two] using S.add_mem S.one_mem S.one_mem,
        by change (2 : k)⁻¹ ∈ S; exact hhalf⟩
    have hD : D ∈ U := ⟨hdS, by simpa [D] using hdiS⟩
    have haU : a ∈ U := (Submonoid.mem_units_iff S.toSubmonoid a).mpr
      ⟨ha, by change (a⁻¹).val ∈ S; simpa only [Units.val_inv_eq_inv_val] using hai⟩
    have hm : (-1 : kˣ) ∈ U := by
      constructor <;> change (-1 : k) ∈ S <;> exact S.neg_mem S.one_mem
    have hγ (b : kˣ) (hb : b ∈ U) : Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ b.val = 1 := by
      have hb' := (Submonoid.mem_units_iff S.toSubmonoid b).mp hb
      exact UnramifiedGaussian.gaussianIndex_integral_unit hnd ψ hc hu hn S hSo hSc hψ hAnn hhalf b hb'.1
        (by have hbi : (b⁻¹).val ∈ S := hb'.2
            simpa only [Units.val_inv_eq_inv_val] using hbi)
    have h2 : Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ 2 = 1 := hγ t ht
    have h2a : Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (2 * a.val) = 1 := hγ (t * a) (U.mul_mem ht haU)
    have hmd : Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (-2 * d) = 1 := by
      simpa [t, D, neg_mul] using hγ ((-1) * t * D) (U.mul_mem (U.mul_mem hm ht) hD)
    have hmda : Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (-2 * d * a.val) = 1 := by
      simpa [t, D, neg_mul] using hγ (((-1) * t * D) * a)
        (U.mul_mem (U.mul_mem (U.mul_mem hm ht) hD) haU)
    have he := QuadraticLocalGaussian.norm_character_gaussian_identity d hd hsq hnd ψ hc hu hn a
    rw [h2, h2a, hmd, hmda, one_mul, mul_one] at he
    exact Circle.coe_injective he

theorem normSign_integral_unit_of_normedField
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k]
    [IsUltrametricDist k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
    (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ)
    (hc : Continuous (fun x : k => ψ x)) (hu : ∀ x : k, ‖ψ x‖ = 1)
    (hn : ∃ x : k, ψ x ≠ 1) (S : Subring k)
    (hSo : IsOpen (S : Set k)) (hSc : IsCompact (S : Set k))
    (hψ : ∀ x ∈ S, ψ x = 1)
    (hAnn : ∀ u, (∀ t ∈ S, ψ (u * t) = 1) → u ∈ S)
    (hhalf : (2 : k)⁻¹ ∈ S) (d : k) (hd : d ≠ 0) (hdS : d ∈ S) (hdiS : d⁻¹ ∈ S)
    (a : kˣ) (ha : a.val ∈ S) (hai : a.val⁻¹ ∈ S) : QuadraticNormCharacter.normSign d a = 1 := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField k with h | ⟨_, rfl⟩
  · exact (hnd h).elim
  · exact normSign_integral_unit hnd ψ hc hu hn S hSo hSc hψ hAnn hhalf d hd hdS hdiS a ha hai

end

end OAI.RepresentationTheory.Theta.Adelic.UnramifiedNormCharacter
