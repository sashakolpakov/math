import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.BallAction
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! # Ball Diffeomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Every actual principal SU element acts by a complex diffeomorphism
of the original ball domain, with bijective native complex derivative. -/

open scoped _root_.Manifold ContDiff

theorem Principal.BallDiffeomorphisms.lineVector_contDiff : ContDiff ℂ ∞ OAI.Geometry.ComplexBall.PrescribedSignsB.lineVector := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℂ ∞ (fun x : OAI.Geometry.ComplexBall.PrescribedSignsB.BallChart => x 0)
    fun_prop
  · change ContDiff ℂ ∞ (fun x : OAI.Geometry.ComplexBall.PrescribedSignsB.BallChart => x 1)
    fun_prop
  · change ContDiff ℂ ∞ (fun _ : OAI.Geometry.ComplexBall.PrescribedSignsB.BallChart => (1 : ℂ))
    fun_prop

theorem Principal.BallDiffeomorphisms.matrixLine_contDiff (m : Matrix (Fin 3) (Fin 3) ℂ) :
    ContDiff ℂ ∞ (fun z : OAI.Geometry.ComplexBall.PrescribedSignsB.BallChart => m.mulVec (OAI.Geometry.ComplexBall.PrescribedSignsB.lineVector z)) :=
  (Matrix.toLin' m).toContinuousLinearMap.contDiff.comp Principal.BallDiffeomorphisms.lineVector_contDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s)

theorem Datum.RankThreePELDatum.lineAction_contDiffAt (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hg : g ∈ Groups.unitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b))
    (z : OAI.Geometry.ComplexBall.PrescribedSignsB.BallChart) (hz : z ∈ P.domain) : ContDiffAt ℂ ∞ (P.lineAction g) z := by
  apply contDiffAt_pi.mpr
  intro i
  let m := (LinearMap.toMatrix' g.toLinearMap).map P.μ
  have hd := Principal.BallDiffeomorphisms.matrixLine_contDiff m
  change ContDiffAt ℂ ∞ (fun w : OAI.Geometry.ComplexBall.PrescribedSignsB.BallChart => m.mulVec (OAI.Geometry.ComplexBall.PrescribedSignsB.lineVector w) i.castSucc / m.mulVec (OAI.Geometry.ComplexBall.PrescribedSignsB.lineVector w) 2) z
  have hn : m.mulVec (OAI.Geometry.ComplexBall.PrescribedSignsB.lineVector z) 2 ≠ 0 := P.lineAction_last_ne_zero g hg z hz
  simp only [div_eq_mul_inv]
  exact (contDiff_pi.mp hd i.castSucc).contDiffAt.mul ((contDiff_pi.mp hd 2).contDiffAt.inv hn)

theorem Datum.RankThreePELDatum.principalBallAction_contMDiff (N : ℕ) (g : Groups.principalSpecialUnitary P.b P.lattice N) :
    ContMDiff 𝓘(ℂ, OAI.Geometry.ComplexBall.PrescribedSignsB.BallChart) 𝓘(ℂ, OAI.Geometry.ComplexBall.PrescribedSignsB.BallChart) ∞ (fun z : P.Domain => g • z) := by
  apply (ContMDiff.subtypeVal_comp_iff P.domainOpen (fun z : P.Domain => g • z)).mp
  intro z
  change ContMDiffAt 𝓘(ℂ, OAI.Geometry.ComplexBall.PrescribedSignsB.BallChart) 𝓘(ℂ, OAI.Geometry.ComplexBall.PrescribedSignsB.BallChart) ∞ (fun w : P.Domain => P.lineAction g.val w.val) z
  apply contMDiffAt_subtype_iff.mpr
  exact (P.lineAction_contDiffAt g.val g.property.2.1 z.val z.property).contMDiffAt

def Datum.RankThreePELDatum.principalBallDiffeomorph (N : ℕ) (g : Groups.principalSpecialUnitary P.b P.lattice N) :
    P.Domain ≃ₘ⟮𝓘(ℂ, OAI.Geometry.ComplexBall.PrescribedSignsB.BallChart), 𝓘(ℂ, OAI.Geometry.ComplexBall.PrescribedSignsB.BallChart)⟯ P.Domain where
  toEquiv := MulAction.toPerm g
  contMDiff_toFun := P.principalBallAction_contMDiff N g
  contMDiff_invFun := P.principalBallAction_contMDiff N g⁻¹

theorem Datum.RankThreePELDatum.principalBallAction_derivative_bijective (N : ℕ) (g : Groups.principalSpecialUnitary P.b P.lattice N) (z : P.Domain) :
    Function.Bijective (mfderiv 𝓘(ℂ, OAI.Geometry.ComplexBall.PrescribedSignsB.BallChart) 𝓘(ℂ, OAI.Geometry.ComplexBall.PrescribedSignsB.BallChart) (fun w : P.Domain => g • w) z) :=
  ((P.principalBallDiffeomorph N g).mfderivToContinuousLinearEquiv (by simp) z).bijective

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
