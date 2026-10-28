import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PeriodAction

/-! # Period Point Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The distinguished first line of the literal prescribed period
subspace determines its ball point. Consequently a transported period
kernel determines the exact arithmetic translate. -/

theorem Reference.PeriodPointDetection.lineVector_point_eq_of_mem (z w : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (h : Geometry.ComplexBall.PrescribedSignsB.lineVector z ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector w}) : z = w := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
  have hone : a = 1 := by simpa [Geometry.ComplexBall.PrescribedSignsB.lineVector] using congrFun ha 2
  rw [hone, one_smul] at ha
  funext i
  fin_cases i
  · exact (congrFun ha 0).symm
  · exact (congrFun ha 1).symm

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

include hP in
theorem Datum.RankThreePELDatum.referencePeriodPoint_of_action_mem (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (hg : g ∈ Groups.unitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b)) (z w : P.Domain)
    (h : ∀ u ∈ P.periodFamily z.val, P.referenceAmbientAction g u ∈ P.periodFamily w.val) :
    w.val = P.lineAction g z.val := by
  classical
  rcases hP with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hf⟩
  let u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) := Pi.single P.distinguished (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val, 0)
  have hu : u ∈ P.periodFamily z.val := by
    apply ((hf z.val z.property).1 u).mpr
    intro i
    by_cases hi : i = P.distinguished
    · subst i
      simp only [u, Pi.single_eq_same, ↓reduceIte]
      exact ⟨Submodule.mem_span_singleton_self _, by simp [Geometry.ComplexBall.PrescribedSignsB.localB]⟩
    · simp [u, hi]
  have hv := (((hf w.val w.property).1 _).mp (h u hu)) P.distinguished
  simp only [↓reduceIte] at hv
  have hl : EmbeddedLinearGroup.embeddedLinearIso g (P.embeddings P.distinguished) (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val) ∈
      Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector w.val} := by
    simpa only [Datum.RankThreePELDatum.referenceAmbientAction, LinearEquiv.piCongrRight_apply,
      LinearEquiv.prodCongr_apply, u, Pi.single_eq_same] using hv.1
  apply Eq.symm
  apply Reference.PeriodPointDetection.lineVector_point_eq_of_mem
  rw [P.lineAction_eq_negativeCoordinate, NegativeLine.negativeLineCoordinate_vector _ (P.lineAction_last_ne_zero g hg z.val z.property)]
  exact (Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector w.val}).smul_mem _ hl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
