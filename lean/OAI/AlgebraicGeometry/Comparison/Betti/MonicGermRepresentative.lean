import OAI.AlgebraicGeometry.Comparison.Betti.GermCoefficientRealization
import OAI.AlgebraicGeometry.Comparison.Betti.GermPolynomialCoefficients

/-! # Monic Germ Representative -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.MonicGermRepresentative.AnalyticLocal

noncomputable section

/-! A monic polynomial of holomorphic germs has an actual holomorphic
family representative of the same fixed degree on a neighborhood. -/

open Set Filter _root_.Polynomial
open scoped _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem monic_representative_eventually (x : E) (Q : (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x)[X]) (hQ : Q.Monic)
    (P : E → ℂ[X]) (d : ℕ) (hd : ∀ y, (P y).natDegree ≤ d)
    (hP : ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs.polynomialRealization x Q = (P : Germ (𝓝 x) ℂ[X])) :
    ∀ᶠ y in 𝓝 x, (P y).Monic ∧ (P y).natDegree = Q.natDegree := by
  have htop : ∀ᶠ y in 𝓝 x, (P y).coeff Q.natDegree = 1 := by
    apply Germ.coe_eq.mp
    rw [GermCoefficientRealization.AnalyticLocal.polynomialRealization_representative_coeff x Q P hP, hQ.coeff_natDegree]
    rfl
  have hhigh : ∀ k : Fin (d + 1), ∀ᶠ y in 𝓝 x,
      Q.natDegree < k.val → (P y).coeff k.val = 0 := by
    intro k
    by_cases hk : Q.natDegree < k.val
    · have hz : ∀ᶠ y in 𝓝 x, (P y).coeff k.val = 0 := by
        apply Germ.coe_eq.mp
        rw [GermCoefficientRealization.AnalyticLocal.polynomialRealization_representative_coeff x Q P hP,
          coeff_eq_zero_of_natDegree_lt hk]
        rfl
      exact hz.mono (fun y hy _ => hy)
    · exact Filter.Eventually.of_forall (fun y hy => (hk hy).elim)
  filter_upwards [htop, eventually_all.mpr hhigh] with y hy ht
  have hle : (P y).natDegree ≤ Q.natDegree := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    by_cases hkd : k ≤ d
    · exact ht ⟨k, by omega⟩ hk
    · exact coeff_eq_zero_of_natDegree_lt ((hd y).trans_lt (lt_of_not_ge hkd))
  have he : (P y).natDegree = Q.natDegree := le_antisymm hle
    (le_natDegree_of_ne_zero (by rw [hy]; exact one_ne_zero))
  refine ⟨?_, he⟩
  change (P y).coeff (P y).natDegree = 1
  rw [he, hy]

theorem polynomial_representative_value (x : E) (Q : (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x)[X])
    (P : E → ℂ[X]) (hP : ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs.polynomialRealization x Q = (P : Germ (𝓝 x) ℂ[X])) :
    P x = Q.map (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.valueHom x) := by
  ext k
  rw [coeff_map]
  exact congrArg Germ.value (GermCoefficientRealization.AnalyticLocal.polynomialRealization_representative_coeff x Q P hP k)

theorem exists_monic_germ_representative (x : E) (Q : (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x)[X]) (hQ : Q.Monic) :
    ∃ (P : E → ℂ[X]) (U : Set E) (hU : IsOpen U) (hx : x ∈ U)
        (hcoeff : ∀ k : ℕ, DifferentiableOn ℂ (fun y => (P y).coeff k) U),
      (∀ y ∈ U, (P y).Monic ∧ (P y).natDegree = Q.natDegree) ∧
      P x = Q.map (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.valueHom x) ∧
      ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs.polynomialOfFamily x P Q.natDegree hU hx hcoeff = Q := by
  obtain ⟨d, P, U, hU, hx, hd, hc, hP⟩ := ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs.exists_polynomial_representative x Q
  obtain ⟨V, hVdata, hV, hxV⟩ := mem_nhds_iff.mp (monic_representative_eventually x Q hQ P d hd hP)
  let T := U ∩ V
  have hT : IsOpen T := hU.inter hV
  have hxT : x ∈ T := ⟨hx, hxV⟩
  have hcoeff : ∀ k : ℕ, DifferentiableOn ℂ (fun y => (P y).coeff k) T :=
    fun k => (hc k).mono inter_subset_left
  have hPT : ∀ y ∈ T, (P y).Monic ∧ (P y).natDegree = Q.natDegree :=
    fun y hy => hVdata hy.2
  refine ⟨P, T, hT, hxT, hcoeff, hPT, polynomial_representative_value x Q P hP, ?_⟩
  apply GermCoefficientRealization.AnalyticLocal.polynomialRealization_injective x
  rw [ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs.realize_polynomialOfFamily x P Q.natDegree hT hxT hcoeff
    (fun y hy => (hPT y hy).2.le), hP]

end

end OAI.AlgebraicGeometry.Comparison.Betti.MonicGermRepresentative.AnalyticLocal
