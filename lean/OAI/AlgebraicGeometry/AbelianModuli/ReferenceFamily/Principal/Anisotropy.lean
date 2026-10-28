import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnisotropicCocharacters
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.ArchimedeanDiscrete
import OAI.NumberTheory.ArithmeticGroups.Trace

/-! # Anisotropy -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The given anisotropic Hermitian form makes the actual rational
algebraic SU group anisotropic, via its faithful CM coordinates. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

theorem Datum.RankThreePELDatum.principalAlgebraicGroup_anisotropic :
    NumberTheory.ArithmeticGroups.Lattices.Algebraic.IsAnisotropic (Geometry.ComplexBall.Connected.ArithmeticQuotient.originalConnectedSemisimpleUnitaryGroup P.b hP.2.1 hP.2.2.1
      P.imaginaryScalar hP.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.1) := by
  let e := Geometry.ComplexBall.IntegralLattice.ArithmeticQuotient.cmCoordinates P.imaginaryScalar hP.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.1
  let r := Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.originalUnitaryRationalEquiv P.b hP.2.1
    P.imaginaryScalar hP.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.1
  let G := Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.originalUnitaryAlgebraicGroup P.b hP.2.1 P.imaginaryScalar hP.2.2.2.2.2.2.2.1
  let q : (Fin 6 → Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) → E := fun v => NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b (e.symm v) (e.symm v)
  have hq (a : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) (v : Fin 6 → Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) :
      q (a • v) = algebraMap (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) E a ^ 2 * q v := by
    change NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b (e.symm (a • v)) (e.symm (a • v)) = _
    rw [map_smul]
    change NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b ((a : E) • e.symm v) ((a : E) • e.symm v) = (a : E) ^ 2 * q v
    rw [NumberTheory.ArithmeticGroups.Trace.CongruenceLevel.hermitian_smul_left, NumberTheory.ArithmeticGroups.Trace.CongruenceLevel.hermitian_smul_right]
    rw [(NumberField.IsCMField.complexConj_eq_self_iff E (a : E)).mpr a.property]
    change (a : E) * ((a : E) * q v) = (a : E) ^ 2 * q v
    ring
  have han (v : Fin 6 → Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) (hv : q v = 0) : v = 0 := by
    apply e.symm.injective
    rw [map_zero]
    exact hP.2.2.2.2.2.1 (e.symm v) hv
  have hinv (g : G.RationalPoints) (v : Fin 6 → Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) :
      q (Matrix.SpecialLinearGroup.toLin' g.val v) = q v := by
    have he : e.symm (Matrix.SpecialLinearGroup.toLin' g.val v) =
        Matrix.SpecialLinearGroup.toLin' (r.symm g).val (e.symm v) := by
      apply e.injective
      rw [e.apply_symm_apply]
      have h := Geometry.ComplexBall.IntegralLattice.ArithmeticQuotient.cmCoordinates_action P.b hP.2.1 P.imaginaryScalar hP.2.2.2.2.2.2.2.1
        hP.2.2.2.2.2.2.1 (r.symm g) (e.symm v)
      change e (Matrix.SpecialLinearGroup.toLin' (r.symm g).val (e.symm v)) =
        Matrix.SpecialLinearGroup.toLin' (r (r.symm g)).val (e (e.symm v)) at h
      rw [r.apply_symm_apply, e.apply_symm_apply] at h
      exact h.symm
    change NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b (e.symm _) (e.symm _) = NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b (e.symm v) (e.symm v)
    rw [he]
    exact (r.symm g).property (e.symm v) (e.symm v)
  intro c K _ ι
  exact AnisotropicCocharacters.cocharacter_trivial_of_anisotropic_invariant G (Geometry.ComplexBall.RealPlaces.ArithmeticQuotient.realEmbedding P.μ)
    (algebraMap (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) E) q hq han hinv c K ι

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
