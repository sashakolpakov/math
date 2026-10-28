import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PrescribedAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AmbientAction

/-! # Period Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The actual arithmetic action carries the entire prescribed reference
period subspace exactly to the period subspace at the translated point. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

include hP in
theorem Datum.RankThreePELDatum.referenceAmbientAction_period_mem
    (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hg : g ∈ Groups.unitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b)) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (hz : z ∈ P.domain)
    (u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) (hu : u ∈ P.periodFamily z) :
    P.referenceAmbientAction g u ∈ P.periodFamily (P.lineAction g z) := by
  rcases hP with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hf⟩
  exact ((hf _ (P.lineAction_mem g hg z hz)).1 _).mpr
    (P.referenceAmbientAction_prescribed g hg z hz u (((hf z hz).1 u).mp hu))

theorem Datum.RankThreePELDatum.lineAction_inv_apply (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hg : g ∈ Groups.unitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b))
    (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (hz : z ∈ P.domain) : P.lineAction g⁻¹ (P.lineAction g z) = z :=
  (P.lineAction_mul g⁻¹ g hg z hz).symm.trans
    ((congrArg (fun h => P.lineAction h z) (inv_mul_cancel g)).trans (P.lineAction_one z))

include hP in
theorem Datum.RankThreePELDatum.referenceAmbientAction_period_map
    (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hg : g ∈ Groups.unitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b)) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (hz : z ∈ P.domain) :
    (P.periodFamily z).map (P.referenceAmbientAction g).toLinearMap = P.periodFamily (P.lineAction g z) := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact P.referenceAmbientAction_period_mem hP g hg z hz u hu
  · intro hv
    have hh := P.referenceAmbientAction_period_mem hP g⁻¹ ((Groups.unitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b)).inv_mem hg)
      (P.lineAction g z) (P.lineAction_mem g hg z hz) v hv
    rw [P.lineAction_inv_apply g hg z hz] at hh
    exact ⟨P.referenceAmbientAction g⁻¹ v, hh, P.referenceAmbientAction_apply_inv g v⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
