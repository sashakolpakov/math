import OAI.AlgebraicGeometry.PELModuli.CMPoints.Models
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Splitting

/-! # Good Reduction -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! The actual arithmetic localization admits the chosen residue map away
from its denominator. All level and polarization exclusions are finite. -/

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : Models.RankThreePELModel E K)

def Models.RankThreePELModel.polarizationDegree (a : M.Family) : ℕ :=
  (∏ i, (M.datum a).polarizationType i) ^ 2

/-- A finite bound incorporating the actual denominator, levels and degrees. -/
def Models.RankThreePELModel.goodReductionBound : ℕ :=
  max M.arithmetic.denominator
    (Finset.univ.sup fun a : M.Family => max (M.level a) (M.polarizationDegree a))

theorem Models.RankThreePELModel.polarizationDegree_pos (hM : M.HasPrescribedBallPeriods) (a : M.Family) :
    0 < M.polarizationDegree a := by
  have hP := (hM.2.2 a).1
  have hp : ∀ i, 0 < (M.datum a).polarizationType i := by
    exact hP.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact pow_pos (Finset.prod_pos (fun i _ => hp i)) _

/-- Extend the specified residue character to the literal arithmetic base. -/
def Models.RankThreePELModel.goodIntegralReduction_of_coprime
    {q : ℕ} [Fact q.Prime] (j : M.QadicChoice q)
    (hd : ¬q ∣ M.arithmetic.denominator)
    (hlevel : ∀ a : M.Family, Nat.Coprime q (M.level a))
    (hpolarization : ∀ a : M.Family, Nat.Coprime q (M.polarizationDegree a)) :
    M.GoodIntegralReduction q j := by
  have hu : IsUnit (j.residue
      (M.arithmetic.denominator : NumberField.RingOfIntegers M.arithmetic.extension.carrier)) := by
    rw [map_natCast, isUnit_iff_ne_zero, ne_eq, ZMod.natCast_eq_zero_iff]
    exact hd
  exact {
    residue := IsLocalization.Away.lift
      (M.arithmetic.denominator : NumberField.RingOfIntegers M.arithmetic.extension.carrier) hu
    residue_compatibility := IsLocalization.Away.lift_comp _ hu
    levelPrimeToQ := hlevel
    polarizationPrimeToQ := hpolarization }

/-- No further reduction data are needed after the prime exceeds the bound. -/
def Models.RankThreePELModel.goodIntegralReduction_of_large_prime (hM : M.HasPrescribedBallPeriods)
    {q : ℕ} [Fact q.Prime] (j : M.QadicChoice q) (hq : M.goodReductionBound < q) :
    M.GoodIntegralReduction q j := by
  have hsmall (a : M.Family) :
      max (M.level a) (M.polarizationDegree a) < q :=
    lt_of_le_of_lt ((Finset.le_sup (f := fun a : M.Family =>
      max (M.level a) (M.polarizationDegree a)) (Finset.mem_univ a)).trans
        (le_max_right _ _)) hq
  apply M.goodIntegralReduction_of_coprime j
  · exact Nat.not_dvd_of_pos_of_lt
      (Nat.pos_of_ne_zero M.arithmetic.denominator_ne_zero)
      (lt_of_le_of_lt (le_max_left _ _) hq)
  · intro a
    apply (Fact.out : q.Prime).coprime_iff_not_dvd.mpr
    exact Nat.not_dvd_of_pos_of_lt
      (lt_of_lt_of_le (by decide : 0 < 3) (hM.2.2 a).2.2.1.1)
      (lt_of_le_of_lt (le_max_left _ _) (hsmall a))
  · intro a
    apply (Fact.out : q.Prime).coprime_iff_not_dvd.mpr
    exact Nat.not_dvd_of_pos_of_lt (M.polarizationDegree_pos hM a)
      (lt_of_le_of_lt (le_max_right _ _) (hsmall a))

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
