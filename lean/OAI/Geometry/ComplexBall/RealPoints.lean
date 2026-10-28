import OAI.Geometry.ComplexBall.RealQuadratic
import OAI.Geometry.ComplexBall.ArithmeticQuotientBoostBall

/-! # Real Points -/

namespace OAI.Geometry.ComplexBall.RealPoints.ArithmeticQuotient

noncomputable section

/-! Topological identification of the real polynomial point group with
complex special unitary matrices. Both directions use explicit coordinates. -/

open scoped Classical
open _root_.Topology

lemma regularUnitaryEquiv_matrix {k : Type} [Field k] (d b : k)
    (g : ArithmeticQuotientEquationsData.SU (starRingEnd (QuadraticAlgebra k d 0)) (algebraMap k _ b)) :
    (ArithmeticQuotientSplitUnitary.regularUnitaryEquiv d b g).val.val = ArithmeticQuotientEquationsData.regularMatrix d g.val.val := rfl

lemma regularUnitaryEquiv_symm_matrix {k : Type} [Field k] (d b : k)
    (g : (ArithmeticQuotientSplitUnitary.unitaryAlgebraicGroup d b).RationalPoints) :
    ((ArithmeticQuotientSplitUnitary.regularUnitaryEquiv d b).symm g).val.val = ArithmeticQuotientEquationsData.decodeMatrix d g.val.val := by
  have h := congrArg (fun x : (ArithmeticQuotientSplitUnitary.unitaryAlgebraicGroup d b).RationalPoints =>
    ArithmeticQuotientEquationsData.decodeMatrix d x.val.val) ((ArithmeticQuotientSplitUnitary.regularUnitaryEquiv d b).apply_symm_apply g)
  rw [regularUnitaryEquiv_matrix, ArithmeticQuotientEquationsData.decode_regularMatrix] at h
  exact h

def realUnitaryPointsEquiv (d r b : ℝ) (hr : r ^ 2 = -d) (hr0 : r ≠ 0) :
    (ArithmeticQuotientSplitUnitary.unitaryAlgebraicGroup d b).RationalPoints ≃* ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) (b : ℂ) :=
  (ArithmeticQuotientSplitUnitary.regularUnitaryEquiv d b).symm.trans (RealQuadratic.ArithmeticQuotient.realQuadraticUnitaryEquiv d r b hr hr0)

lemma realUnitaryPointsEquiv_entry (d r b : ℝ) (hr : r ^ 2 = -d) (hr0 : r ≠ 0)
    (g : (ArithmeticQuotientSplitUnitary.unitaryAlgebraicGroup d b).RationalPoints) (i j : Fin 3) :
    (realUnitaryPointsEquiv d r b hr hr0 g).val i j =
      RealQuadratic.ArithmeticQuotient.realQuadraticHom d r hr (ArithmeticQuotientEquationsData.decodeMatrix d g.val.val i j) := by
  change (RealQuadratic.ArithmeticQuotient.realQuadraticUnitaryEquiv d r b hr hr0
    ((ArithmeticQuotientSplitUnitary.regularUnitaryEquiv d b).symm g)).val i j = _
  rw [RealQuadratic.ArithmeticQuotient.realQuadraticUnitaryEquiv_entry]
  exact congrArg (fun M => RealQuadratic.ArithmeticQuotient.realQuadraticHom d r hr (M i j))
    (regularUnitaryEquiv_symm_matrix d b g)

lemma realUnitaryPointsEquiv_symm_matrix (d r b : ℝ) (hr : r ^ 2 = -d) (hr0 : r ≠ 0)
    (g : ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) (b : ℂ)) :
    ((realUnitaryPointsEquiv d r b hr hr0).symm g).val.val =
      ArithmeticQuotientEquationsData.regularMatrix d (fun i j => RealQuadratic.ArithmeticQuotient.realQuadraticInverse d r (g.val i j)) := by
  change (ArithmeticQuotientSplitUnitary.regularUnitaryEquiv d b ((RealQuadratic.ArithmeticQuotient.realQuadraticUnitaryEquiv d r b hr hr0).symm g)).val.val = _
  rw [regularUnitaryEquiv_matrix]
  apply congrArg (ArithmeticQuotientEquationsData.regularMatrix d)
  apply Matrix.ext
  intro i j
  exact RealQuadratic.ArithmeticQuotient.realQuadraticUnitaryEquiv_symm_entry d r b hr hr0 g i j

lemma realUnitaryPointsEquiv_continuous (d r b : ℝ) (hr : r ^ 2 = -d) (hr0 : r ≠ 0) :
    Continuous (realUnitaryPointsEquiv d r b hr hr0) := by
  apply IsInducing.subtypeVal.continuous_iff.mpr
  apply IsInducing.subtypeVal.continuous_iff.mpr
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun g : (ArithmeticQuotientSplitUnitary.unitaryAlgebraicGroup d b).RationalPoints =>
    (realUnitaryPointsEquiv d r b hr hr0 g).val i j)
  simp_rw [realUnitaryPointsEquiv_entry, RealQuadratic.ArithmeticQuotient.realQuadraticHom_apply]
  dsimp [ArithmeticQuotientEquationsData.decodeMatrix]
  fun_prop

lemma realUnitaryPointsEquiv_symm_continuous (d r b : ℝ) (hr : r ^ 2 = -d) (hr0 : r ≠ 0) :
    Continuous (realUnitaryPointsEquiv d r b hr hr0).symm := by
  apply IsInducing.subtypeVal.continuous_iff.mpr
  apply IsInducing.subtypeVal.continuous_iff.mpr
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun g : ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) (b : ℂ) =>
    ((realUnitaryPointsEquiv d r b hr hr0).symm g).val.val i j)
  simp_rw [realUnitaryPointsEquiv_symm_matrix]
  obtain ⟨⟨i, a⟩, rfl⟩ := ArithmeticQuotientEquationsData.pairIndex.surjective i
  obtain ⟨⟨j, c⟩, rfl⟩ := ArithmeticQuotientEquationsData.pairIndex.surjective j
  suffices hc : Continuous (fun g : ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) (b : ℂ) =>
      ArithmeticQuotientEquationsData.quadraticRegular d (RealQuadratic.ArithmeticQuotient.realQuadraticInverse d r (g.val i j)) a c) by
    exact hc.congr (fun g => (ArithmeticQuotientEquationsData.regularMatrix_entry d
      (fun i j => RealQuadratic.ArithmeticQuotient.realQuadraticInverse d r (g.val i j)) i j a c).symm)
  fin_cases a <;> fin_cases c <;> dsimp [ArithmeticQuotientEquationsData.quadraticRegular, RealQuadratic.ArithmeticQuotient.realQuadraticInverse] <;> fun_prop

def realUnitaryPointsContinuousEquiv (d r b : ℝ) (hr : r ^ 2 = -d) (hr0 : r ≠ 0) :
    (ArithmeticQuotientSplitUnitary.unitaryAlgebraicGroup d b).RationalPoints ≃ₜ* ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) (b : ℂ) where
  toMulEquiv := realUnitaryPointsEquiv d r b hr hr0
  continuous_toFun := realUnitaryPointsEquiv_continuous d r b hr hr0
  continuous_invFun := realUnitaryPointsEquiv_symm_continuous d r b hr hr0

def negativeRealUnitaryPointsEquiv (d b : ℝ) (hd : d < 0) :
    (ArithmeticQuotientSplitUnitary.unitaryAlgebraicGroup d b).RationalPoints ≃ₜ* ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) (b : ℂ) :=
  realUnitaryPointsContinuousEquiv d (Real.sqrt (-d)) b
    (Real.sq_sqrt (by linarith)) (ne_of_gt (Real.sqrt_pos.mpr (by linarith)))

theorem realUnitaryPoints_compact_of_positive (d b : ℝ) (hd : d < 0) (hb : 0 < b) :
    CompactSpace (ArithmeticQuotientSplitUnitary.unitaryAlgebraicGroup d b).RationalPoints := by
  let : CompactSpace (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) (b : ℂ)) :=
    ArithmeticQuotientBoostBall.compact_complex_unitary_of_positive (b : ℂ) hb
  exact (negativeRealUnitaryPointsEquiv d b hd).symm.toHomeomorph.compactSpace

end

end OAI.Geometry.ComplexBall.RealPoints.ArithmeticQuotient
