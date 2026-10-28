import OAI.RepresentationTheory.Theta.Geometric.Reference.Domain

/-! # Quotient -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Explicit quotient coordinates for the reference period family. The
active block has two coordinates from the first embedding and one from
its conjugate; each compact block retains the prescribed whole summand. -/

open scoped Classical

abbrev Period.Quotient.PeriodBlock := Fin 3 → ℂ

def Period.Quotient.activePeriodProjection (b : ℂ) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) :
    (Period.Quotient.PeriodBlock × Period.Quotient.PeriodBlock) →ₗ[ℂ] Period.Quotient.PeriodBlock where
  toFun u := ![u.1 0 - z 0 * u.1 2, u.1 1 - z 1 * u.1 2,
    z 0 * u.2 0 + z 1 * u.2 1 + b * u.2 2]
  map_add' u v := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c u := by ext i; fin_cases i <;> simp <;> ring

theorem Period.Quotient.firstPeriod_kernel (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (u : Period.Quotient.PeriodBlock) :
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

theorem Period.Quotient.activePeriodProjection_kernel (b : ℂ) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (u : Period.Quotient.PeriodBlock × Period.Quotient.PeriodBlock) :
    Period.Quotient.activePeriodProjection b z u = 0 ↔
      u.1 ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z} ∧
        z 0 * u.2 0 + z 1 * u.2 1 + b * u.2 2 = 0 := by
  have h : Period.Quotient.activePeriodProjection b z u = 0 ↔
      (u.1 0 - z 0 * u.1 2 = 0 ∧ u.1 1 - z 1 * u.1 2 = 0) ∧
        z 0 * u.2 0 + z 1 * u.2 1 + b * u.2 2 = 0 := by
    simp only [Period.Quotient.activePeriodProjection, LinearMap.coe_mk, AddHom.coe_mk, funext_iff]
    simp [Fin.forall_fin_succ, and_assoc]
  rw [h, Period.Quotient.firstPeriod_kernel]

def Period.Quotient.activePeriodSection (b : ℂ) : Period.Quotient.PeriodBlock →ₗ[ℂ] (Period.Quotient.PeriodBlock × Period.Quotient.PeriodBlock) where
  toFun t := (![t 0, t 1, 0], ![0, 0, t 2 / b])
  map_add' u v := by ext i <;> fin_cases i <;> simp [add_div]
  map_smul' c u := by ext i <;> fin_cases i <;> simp [mul_div_assoc]

theorem Period.Quotient.activePeriodProjection_section (b : ℂ) (hb : b ≠ 0)
    (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (t : Period.Quotient.PeriodBlock) :
    Period.Quotient.activePeriodProjection b z (Period.Quotient.activePeriodSection b t) = t := by
  ext i
  fin_cases i <;> simp only [Period.Quotient.activePeriodProjection, Period.Quotient.activePeriodSection, LinearMap.coe_mk, AddHom.coe_mk]
  · simp
  · simp
  · change z 0 * 0 + z 1 * 0 + b * (t 2 / b) = t 2
    rw [mul_zero, mul_zero, zero_add, zero_add, mul_comm]
    exact div_mul_cancel₀ _ hb

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

abbrev Data.ActiveHeckeThetaData.PeriodQuotientCoordinates := Fin s → Period.Quotient.PeriodBlock

def Data.ActiveHeckeThetaData.periodProjection (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) :
    Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) →ₗ[ℂ] Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s) where
  toFun u i := if i = D.pel.reference.distinguished then
    Period.Quotient.activePeriodProjection (D.pel.reference.μ D.pel.reference.b) z (u i)
    else if D.pel.reference.compactSigns i then (u i).1 else (u i).2
  map_add' u v := by
    funext i
    dsimp
    split_ifs <;> simp only [map_add]
  map_smul' c u := by
    funext i
    dsimp
    split_ifs <;> simp only [map_smul]

def Data.ActiveHeckeThetaData.periodSection : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s) →ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) where
  toFun t i := if i = D.pel.reference.distinguished then
    Period.Quotient.activePeriodSection (D.pel.reference.μ D.pel.reference.b) (t i)
    else if D.pel.reference.compactSigns i then (t i, 0) else (0, t i)
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

theorem Data.ActiveHeckeThetaData.periodProjection_section (hg : D.pel.HasIntegralModelGeometry) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (t : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) : D.periodProjection z (D.periodSection t) = t := by
  have hb : D.pel.reference.μ D.pel.reference.b ≠ 0 := by
    exact (map_ne_zero D.pel.reference.μ).mpr hg.reference_admissible.2.2.1
  funext i
  dsimp [Data.ActiveHeckeThetaData.periodProjection, Data.ActiveHeckeThetaData.periodSection]
  split_ifs
  · exact Period.Quotient.activePeriodProjection_section _ hb z (t i)
  · rfl
  · rfl

theorem Data.ActiveHeckeThetaData.periodProjection_kernel (hg : D.pel.HasIntegralModelGeometry) (z : D.domain) :
    (D.periodProjection z.val).ker = D.pel.reference.periodFamily z.val := by
  rcases hg.reference_admissible with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hperiod⟩
  have hp := (hperiod z.val (by rw [D.reference_domain_eq]; exact z.property)).1
  ext u
  change D.periodProjection z.val u = 0 ↔ _
  rw [hp]
  rw [funext_iff]
  simp only [Pi.zero_apply]
  unfold Geometry.ComplexBall.PrescribedSignsB.Prescribed
  apply forall_congr'
  intro i
  by_cases hi : i = D.pel.reference.distinguished
  · subst i
    simp only [Data.ActiveHeckeThetaData.periodProjection, LinearMap.coe_mk, AddHom.coe_mk, ↓reduceIte]
    rw [Period.Quotient.activePeriodProjection_kernel, NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.localB_diagonal]
    simp [Geometry.ComplexBall.PrescribedSignsB.lineVector, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.μ]
  · by_cases hd : D.pel.reference.compactSigns i = true
    · simp only [Data.ActiveHeckeThetaData.periodProjection, LinearMap.coe_mk, AddHom.coe_mk, hi, ite_false, hd, ite_true]
    · simp only [Data.ActiveHeckeThetaData.periodProjection, LinearMap.coe_mk, AddHom.coe_mk, hi, ite_false, hd, Bool.false_eq_true]

theorem Data.ActiveHeckeThetaData.periodProjection_differentiable :
    Differentiable ℂ (fun p : Geometry.ComplexBall.PrescribedSignsB.BallChart × Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) =>
      D.periodProjection p.1 p.2) := by
  apply differentiable_pi.mpr
  intro i
  by_cases hi : i = D.pel.reference.distinguished
  · simp only [Data.ActiveHeckeThetaData.periodProjection, LinearMap.coe_mk, AddHom.coe_mk, hi, ite_true]
    apply differentiable_pi.mpr
    intro j
    fin_cases j
    · change Differentiable ℂ (fun p : Geometry.ComplexBall.PrescribedSignsB.BallChart × Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) =>
        (p.2 D.pel.reference.distinguished).1 0 - p.1 0 * (p.2 D.pel.reference.distinguished).1 2)
      fun_prop
    · change Differentiable ℂ (fun p : Geometry.ComplexBall.PrescribedSignsB.BallChart × Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) =>
        (p.2 D.pel.reference.distinguished).1 1 - p.1 1 * (p.2 D.pel.reference.distinguished).1 2)
      fun_prop
    · change Differentiable ℂ (fun p : Geometry.ComplexBall.PrescribedSignsB.BallChart × Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) =>
        p.1 0 * (p.2 D.pel.reference.distinguished).2 0 +
        p.1 1 * (p.2 D.pel.reference.distinguished).2 1 +
        D.pel.reference.μ D.pel.reference.b * (p.2 D.pel.reference.distinguished).2 2)
      fun_prop
  · by_cases hd : D.pel.reference.compactSigns i = true
    · simp only [Data.ActiveHeckeThetaData.periodProjection, LinearMap.coe_mk, AddHom.coe_mk, hi, ite_false, hd, ite_true]
      fun_prop
    · simp only [Data.ActiveHeckeThetaData.periodProjection, LinearMap.coe_mk, AddHom.coe_mk, hi, ite_false, hd, Bool.false_eq_true]
      fun_prop

end

end OAI.RepresentationTheory.Theta.Geometric
