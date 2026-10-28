import OAI.AlgebraicGeometry.DivisorClass.Chern.LogCech

/-! # Chern Log Additivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChernLogAdditivity

noncomputable section

section

/-! Products of actual transition cocycles add their rational Chern
classes. The identity is proved through the logarithmic defect and the
linear Cech-to-singular comparison. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech

variable {ι : Type} (X : TopCat.{0}) (U : ι → Opens X)

theorem exponentialCocycle_add (l m : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain X U)
    (hl : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle X U l) (hm : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle X U m) :
    DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle X U (l + m) := by
  intro a x
  change Complex.exp (DivisorClass.Chern.LogCech.RationalCech.edgeLog X U l 2 a x + DivisorClass.Chern.LogCech.RationalCech.edgeLog X U m 2 a x) *
    Complex.exp (DivisorClass.Chern.LogCech.RationalCech.edgeLog X U l 0 a x + DivisorClass.Chern.LogCech.RationalCech.edgeLog X U m 0 a x) =
      Complex.exp (DivisorClass.Chern.LogCech.RationalCech.edgeLog X U l 1 a x + DivisorClass.Chern.LogCech.RationalCech.edgeLog X U m 1 a x)
  simp only [Complex.exp_add]
  calc
    _ = (Complex.exp (DivisorClass.Chern.LogCech.RationalCech.edgeLog X U l 2 a x) * Complex.exp (DivisorClass.Chern.LogCech.RationalCech.edgeLog X U l 0 a x)) *
      (Complex.exp (DivisorClass.Chern.LogCech.RationalCech.edgeLog X U m 2 a x) * Complex.exp (DivisorClass.Chern.LogCech.RationalCech.edgeLog X U m 0 a x)) := by ring
    _ = _ := by rw [hl a x, hm a x]

theorem logDefectCech_add (l m : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain X U)
    (hl : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle X U l) (hm : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle X U m) :
    DivisorClass.Chern.LogCech.RationalCech.logDefectCech X U (l + m) (exponentialCocycle_add X U l m hl hm) =
      DivisorClass.Chern.LogCech.RationalCech.logDefectCech X U l hl + DivisorClass.Chern.LogCech.RationalCech.logDefectCech X U m hm := by
  apply DivisorClass.Chern.LogCech.RationalCech.periodCechMap_injective X U 2
  simp only [map_add, DivisorClass.Chern.LogCech.RationalCech.periodMap_logDefectCech]

theorem logDefectCocycle_add (l m : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain X U)
    (hl : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle X U l) (hm : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle X U m) :
    DivisorClass.Chern.LogCech.RationalCech.logDefectCocycle X U (l + m) (exponentialCocycle_add X U l m hl hm) =
      DivisorClass.Chern.LogCech.RationalCech.logDefectCocycle X U l hl + DivisorClass.Chern.LogCech.RationalCech.logDefectCocycle X U m hm := by
  apply Subtype.ext
  exact logDefectCech_add X U l m hl hm

theorem logarithmicSingularClass_add (hU : ∀ x : X, ∃ i, x ∈ U i)
    (l m : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain X U) (hl : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle X U l) (hm : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle X U m) :
    DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass X U hU (l + m) (exponentialCocycle_add X U l m hl hm) =
      DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass X U hU l hl + DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass X U hU m hm := by
  unfold DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass DivisorClass.Chern.Cech.Obj.RationalCech.singularClassOfCechCocycle
  rw [logDefectCocycle_add, map_add, map_add]

end

/-! Powers of transition cocycles multiply their actual logarithmic class. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech

variable {ι : Type} (X : TopCat.{0}) (U : ι → Opens X)

theorem exponentialCocycle_zero : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle X U 0 := by
  intro a x
  change Complex.exp 0 * Complex.exp 0 = Complex.exp 0
  rw [Complex.exp_zero, one_mul]

theorem exponentialCocycle_nsmul (l : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain X U)
    (hl : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle X U l) (n : ℕ) : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle X U (n • l) := by
  induction n with
  | zero => simpa only [zero_nsmul] using exponentialCocycle_zero X U
  | succ n ih =>
    rw [succ_nsmul]
    exact exponentialCocycle_add X U (n • l) l ih hl

theorem logarithmicSingularClass_zero (hU : ∀ x : X, ∃ i, x ∈ U i) :
    DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass X U hU 0 (exponentialCocycle_zero X U) = 0 := by
  have hd : DivisorClass.Chern.LogCech.RationalCech.logDefectCech X U 0 (exponentialCocycle_zero X U) = 0 := by
    apply DivisorClass.Chern.LogCech.RationalCech.periodCechMap_injective X U 2
    rw [DivisorClass.Chern.LogCech.RationalCech.periodMap_logDefectCech, map_zero, map_zero]
  have hc : DivisorClass.Chern.LogCech.RationalCech.logDefectCocycle X U 0 (exponentialCocycle_zero X U) = 0 := Subtype.ext hd
  unfold DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass DivisorClass.Chern.Cech.Obj.RationalCech.singularClassOfCechCocycle
  rw [hc, map_zero, map_zero]

theorem logarithmicSingularClass_nsmul (hU : ∀ x : X, ∃ i, x ∈ U i)
    (l : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain X U) (hl : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle X U l) (n : ℕ) :
    DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass X U hU (n • l) (exponentialCocycle_nsmul X U l hl n) =
      n • DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass X U hU l hl := by
  induction n with
  | zero => simpa only [zero_nsmul] using logarithmicSingularClass_zero X U hU
  | succ n ih =>
    simp only [succ_nsmul]
    exact (logarithmicSingularClass_add X U hU (n • l) l
      (exponentialCocycle_nsmul X U l hl n) hl).trans (congrArg (fun x => x + _) ih)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChernLogAdditivity
