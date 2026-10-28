import OAI.NumberTheory.PadicHodge.WeakAdmissibility.DividedPowerCompletion
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.DividedPowerRelation

/-! # Crystalline Relation -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.CrystallineRelation

noncomputable section

/-! The formal relation xi-X vanishes in the actual crystalline completion. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaKernel OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaDividedPowers OAI.NumberTheory.PadicHodge.WeakAdmissibility.DividedPowerCompletion OAI.NumberTheory.PadicHodge.WeakAdmissibility.DividedPowerRelation
variable (p : ℕ) [Fact p.Prime]

theorem gammaXi_one : ThetaDividedPowers.gammaXi p 1 = algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p) (ThetaKernel.thetaGenerator p) := by
  simp [ThetaDividedPowers.gammaXi]

theorem thetaGenerator_mul_dividedPower (n : ℕ) :
    algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) (ThetaKernel.thetaGenerator p) * ThetaDividedPowers.thetaDividedPower p n =
      (n + 1 : ℕ) * ThetaDividedPowers.thetaDividedPower p (n + 1) := by
  apply Subtype.ext
  change algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p) (ThetaKernel.thetaGenerator p) * ThetaDividedPowers.gammaXi p n =
    (n + 1 : ℕ) * ThetaDividedPowers.gammaXi p (n + 1)
  have he := ThetaDividedPowers.gammaXi_mul p 1 n
  rw [gammaXi_one] at he
  simpa only [Nat.choose_one_right, Nat.add_comm] using he

theorem dividedPowerCombination_relation :
    (DividedPowerCompletion.dividedPowerCombination p).comp (DividedPowerRelation.dividedPowerRelation (ThetaKernel.thetaGenerator p)) = 0 := by
  apply Finsupp.lhom_ext
  intro n a
  change DividedPowerCompletion.dividedPowerCombination p
    (ThetaKernel.thetaGenerator p • Finsupp.single n a - DividedPowerRelation.dividedPowerShift (Finsupp.single n a)) = 0
  rw [map_sub, map_smul]
  change ThetaKernel.thetaGenerator p • Finsupp.linearCombination (Logarithm.PeriodRings.AInf p) (ThetaDividedPowers.thetaDividedPower p) (Finsupp.single n a) -
    Finsupp.linearCombination (Logarithm.PeriodRings.AInf p) (ThetaDividedPowers.thetaDividedPower p)
      (Finsupp.linearCombination (Logarithm.PeriodRings.AInf p) (fun i : ℕ => Finsupp.single (i + 1) (i + 1 : Logarithm.PeriodRings.AInf p))
        (Finsupp.single n a)) = 0
  rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single, map_smul, Finsupp.linearCombination_single]
  simp only [Algebra.smul_def]
  rw [mul_left_comm, thetaGenerator_mul_dividedPower]
  simp only [map_add, map_natCast, map_one, Nat.cast_add, Nat.cast_one, sub_self]

theorem dividedPowerToCompletion_relation :
    (DividedPowerCompletion.dividedPowerToCompletion p).comp (DividedPowerRelation.dividedPowerRelation (ThetaKernel.thetaGenerator p)) = 0 := by
  apply LinearMap.ext
  intro f
  have he := LinearMap.congr_fun (dividedPowerCombination_relation p) f
  change DividedPowerCompletion.dividedPowerCombination p (DividedPowerRelation.dividedPowerRelation (ThetaKernel.thetaGenerator p) f) = 0 at he
  change algebraMap (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.ACris p)
    (DividedPowerCompletion.dividedPowerCombination p (DividedPowerRelation.dividedPowerRelation (ThetaKernel.thetaGenerator p) f)) = 0
  rw [he, map_zero]

theorem completedDividedPowers_relation
    (x : AdicCompletion (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (ℕ →₀ Logarithm.PeriodRings.AInf p)) :
    DividedPowerCompletion.completedDividedPowers p
      (AdicCompletion.map (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (DividedPowerRelation.dividedPowerRelation (ThetaKernel.thetaGenerator p)) x) = 0 := by
  have he : AdicCompletion.map (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (DividedPowerCompletion.dividedPowerToCompletion p)
      (AdicCompletion.map (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (DividedPowerRelation.dividedPowerRelation (ThetaKernel.thetaGenerator p)) x) = 0 := by
    rw [AdicCompletion.map_comp_apply, dividedPowerToCompletion_relation, AdicCompletion.map_zero, LinearMap.zero_apply]
  change (AdicCompletion.ofLinearEquiv (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (Logarithm.PeriodRings.ACris p)).symm
    (AdicCompletion.map (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (DividedPowerCompletion.dividedPowerToCompletion p)
      (AdicCompletion.map (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (DividedPowerRelation.dividedPowerRelation (ThetaKernel.thetaGenerator p)) x)) = 0
  exact (congrArg (AdicCompletion.ofLinearEquiv (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (Logarithm.PeriodRings.ACris p)).symm he).trans (map_zero _)

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.CrystallineRelation
