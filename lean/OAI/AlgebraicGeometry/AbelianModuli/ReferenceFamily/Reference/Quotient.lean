import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum
import OAI.NumberTheory.ArithmeticGroups.Diagonal

/-! # Quotient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Explicit quotient coordinates for the reference period family. The
active block has two coordinates from the first embedding and one from
its conjugate; each compact block retains the prescribed whole summand. -/

open scoped Classical

abbrev Reference.Quotient.PeriodBlock := Fin 3 → ℂ

def Reference.Quotient.activePeriodProjection (b : ℂ) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) :
    (Reference.Quotient.PeriodBlock × Reference.Quotient.PeriodBlock) →ₗ[ℂ] Reference.Quotient.PeriodBlock where
  toFun u := ![u.1 0 - z 0 * u.1 2, u.1 1 - z 1 * u.1 2,
    z 0 * u.2 0 + z 1 * u.2 1 + b * u.2 2]
  map_add' u v := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c u := by ext i; fin_cases i <;> simp <;> ring

theorem Reference.Quotient.firstPeriod_kernel (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (u : Reference.Quotient.PeriodBlock) :
    (u 0 - z 0 * u 2 = 0 ∧ u 1 - z 1 * u 2 = 0) ↔
      u ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z} := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨h₀, h₁⟩
    refine ⟨u 2, ?_⟩
    ext i
    fin_cases i
    · change u 2 * z 0 = u 0
      rw [mul_comm]
      exact (sub_eq_zero.mp h₀).symm
    · change u 2 * z 1 = u 1
      rw [mul_comm]
      exact (sub_eq_zero.mp h₁).symm
    · simp [Geometry.ComplexBall.PrescribedSignsB.lineVector]
  · rintro ⟨a, rfl⟩
    simp [Geometry.ComplexBall.PrescribedSignsB.lineVector, mul_comm]

theorem Reference.Quotient.activePeriodProjection_kernel (b : ℂ) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (u : Reference.Quotient.PeriodBlock × Reference.Quotient.PeriodBlock) :
    Reference.Quotient.activePeriodProjection b z u = 0 ↔
      u.1 ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z} ∧
        z 0 * u.2 0 + z 1 * u.2 1 + b * u.2 2 = 0 := by
  have h : Reference.Quotient.activePeriodProjection b z u = 0 ↔
      (u.1 0 - z 0 * u.1 2 = 0 ∧ u.1 1 - z 1 * u.1 2 = 0) ∧
        z 0 * u.2 0 + z 1 * u.2 1 + b * u.2 2 = 0 := by
    simp only [Reference.Quotient.activePeriodProjection, LinearMap.coe_mk, AddHom.coe_mk, funext_iff]
    simp [Fin.forall_fin_succ, and_assoc]
  rw [h, Reference.Quotient.firstPeriod_kernel]

def Reference.Quotient.activePeriodSection (b : ℂ) : Reference.Quotient.PeriodBlock →ₗ[ℂ] (Reference.Quotient.PeriodBlock × Reference.Quotient.PeriodBlock) where
  toFun t := (![t 0, t 1, 0], ![0, 0, t 2 / b])
  map_add' u v := by ext i <;> fin_cases i <;> simp [add_div]
  map_smul' c u := by ext i <;> fin_cases i <;> simp [mul_div_assoc]

theorem Reference.Quotient.activePeriodProjection_section (b : ℂ) (hb : b ≠ 0)
    (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (t : Reference.Quotient.PeriodBlock) :
    Reference.Quotient.activePeriodProjection b z (Reference.Quotient.activePeriodSection b t) = t := by
  ext i
  fin_cases i <;> simp only [Reference.Quotient.activePeriodProjection, Reference.Quotient.activePeriodSection, LinearMap.coe_mk, AddHom.coe_mk]
  · simp
  · simp
  · change z 0 * 0 + z 1 * 0 + b * (t 2 / b) = t 2
    rw [mul_zero, mul_zero, zero_add, zero_add, mul_comm]
    exact div_mul_cancel₀ _ hb

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} (P : Datum.RankThreePELDatum E s)

abbrev Datum.RankThreePELDatum.PeriodQuotientCoordinates := Fin s → Reference.Quotient.PeriodBlock

def Datum.RankThreePELDatum.periodProjection (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) :
    Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) →ₗ[ℂ] Datum.RankThreePELDatum.PeriodQuotientCoordinates (s := s) where
  toFun u i := if i = P.distinguished then
    Reference.Quotient.activePeriodProjection (P.μ P.b) z (u i)
    else if P.compactSigns i then (u i).1 else (u i).2
  map_add' u v := by
    funext i
    dsimp
    split_ifs <;> simp only [map_add]
  map_smul' c u := by
    funext i
    dsimp
    split_ifs <;> simp only [map_smul]

def Datum.RankThreePELDatum.periodSection : Datum.RankThreePELDatum.PeriodQuotientCoordinates (s := s) →ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) where
  toFun t i := if i = P.distinguished then
    Reference.Quotient.activePeriodSection (P.μ P.b) (t i)
    else if P.compactSigns i then (t i, 0) else (0, t i)
  map_add' u v := by
    funext i
    dsimp
    split_ifs
    · exact map_add _ _ _
    · exact Prod.ext rfl (zero_add 0).symm
    · exact Prod.ext (zero_add 0).symm rfl
  map_smul' c u := by
    funext i
    dsimp
    split_ifs
    · exact map_smul _ _ _
    · exact Prod.ext rfl (smul_zero c).symm
    · exact Prod.ext (smul_zero c).symm rfl

theorem Datum.RankThreePELDatum.periodProjection_section (hP : P.IsAdmissible) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (t : Datum.RankThreePELDatum.PeriodQuotientCoordinates (s := s)) : P.periodProjection z (P.periodSection t) = t := by
  have hb : P.μ P.b ≠ 0 := by
    exact (map_ne_zero P.μ).mpr hP.2.2.1
  funext i
  dsimp [Datum.RankThreePELDatum.periodProjection, Datum.RankThreePELDatum.periodSection]
  split_ifs
  · exact Reference.Quotient.activePeriodProjection_section _ hb z (t i)
  · rfl
  · rfl

theorem Datum.RankThreePELDatum.periodProjection_kernel (hP : P.IsAdmissible) (z : P.domain) :
    (P.periodProjection z.val).ker = P.periodFamily z.val := by
  rcases hP with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hperiod⟩
  have hp := (hperiod z.val z.property).1
  ext u
  change P.periodProjection z.val u = 0 ↔ _
  rw [hp]
  rw [funext_iff]
  simp only [Pi.zero_apply]
  unfold Geometry.ComplexBall.PrescribedSignsB.Prescribed
  apply forall_congr'
  intro i
  by_cases hi : i = P.distinguished
  · subst i
    simp only [Datum.RankThreePELDatum.periodProjection, LinearMap.coe_mk, AddHom.coe_mk, ↓reduceIte]
    rw [Reference.Quotient.activePeriodProjection_kernel, NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.localB_diagonal]
    simp [Geometry.ComplexBall.PrescribedSignsB.lineVector, Datum.RankThreePELDatum.μ]
  · by_cases hd : P.compactSigns i = true
    · simp only [Datum.RankThreePELDatum.periodProjection, LinearMap.coe_mk, AddHom.coe_mk, hi, ite_false, hd, ite_true]
    · simp only [Datum.RankThreePELDatum.periodProjection, LinearMap.coe_mk, AddHom.coe_mk, hi, ite_false, hd, Bool.false_eq_true]

omit [NumberField E] [NumberField.IsCMField E] in
theorem Datum.RankThreePELDatum.periodProjection_differentiable :
    Differentiable ℂ (fun p : Geometry.ComplexBall.PrescribedSignsB.BallChart × Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) =>
      P.periodProjection p.1 p.2) := by
  apply differentiable_pi.mpr
  intro i
  by_cases hi : i = P.distinguished
  · simp only [Datum.RankThreePELDatum.periodProjection, LinearMap.coe_mk, AddHom.coe_mk, hi, ite_true]
    apply differentiable_pi.mpr
    intro j
    fin_cases j
    · change Differentiable ℂ (fun p : Geometry.ComplexBall.PrescribedSignsB.BallChart × Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) =>
        (p.2 P.distinguished).1 0 - p.1 0 * (p.2 P.distinguished).1 2)
      fun_prop
    · change Differentiable ℂ (fun p : Geometry.ComplexBall.PrescribedSignsB.BallChart × Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) =>
        (p.2 P.distinguished).1 1 - p.1 1 * (p.2 P.distinguished).1 2)
      fun_prop
    · change Differentiable ℂ (fun p : Geometry.ComplexBall.PrescribedSignsB.BallChart × Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) =>
        p.1 0 * (p.2 P.distinguished).2 0 +
        p.1 1 * (p.2 P.distinguished).2 1 +
        P.μ P.b * (p.2 P.distinguished).2 2)
      fun_prop
  · by_cases hd : P.compactSigns i = true
    · simp only [Datum.RankThreePELDatum.periodProjection, LinearMap.coe_mk, AddHom.coe_mk, hi, ite_false, hd, ite_true]
      fun_prop
    · simp only [Datum.RankThreePELDatum.periodProjection, LinearMap.coe_mk, AddHom.coe_mk, hi, ite_false, hd, Bool.false_eq_true]
      fun_prop

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
