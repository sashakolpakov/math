import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ComplexTransition

/-! # Compact Complex -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CompactComplex.CM

noncomputable section

section

/-! ThetaCycle: the compact period coordinates act as the actual selected-line projectors. -/

open scoped Classical _root_.Matrix
open _root_.Module

variable {E : Type*} [Field E] [Algebra ℚ E]

theorem local_basis_matrix_isUnit (σ : E →ₐ[ℚ] ℂ) (b : Basis (Fin 2) E (Analysis.DifferentialForms.Coordinates.LocalApproximation.W E)) :
    IsUnit (Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix σ b) := by
  have hm : Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix σ b =
      (LinearMap.toMatrix' b.equivFun.symm.toLinearMap).map σ := by
    ext i j
    simp only [Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix, Matrix.map_apply, LinearMap.toMatrix'_apply,
      LinearEquiv.coe_coe, b.equivFun_symm_apply]
    fin_cases j <;> simp
  rw [hm]
  exact (LinearMap.isUnit_toMatrix'_iff.mpr
    ((Module.End.isUnit_iff _).mpr b.equivFun.symm.bijective)).map σ.toRingHom.mapMatrix

def boolDiagonal (d : Fin 2 → Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => if d i then 1 else 0)

theorem bool_diagonal_complement (d : Fin 2 → Bool) :
    1 - boolDiagonal d = boolDiagonal (fun i => !d i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    cases h : d i <;> simp [boolDiagonal, h]
  · simp [boolDiagonal, hij]

theorem bool_diagonal_idempotent (d : Fin 2 → Bool) :
    boolDiagonal d * boolDiagonal d = boolDiagonal d := by
  unfold boolDiagonal
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  cases d i <;> simp

theorem conjugate_bool_diagonal (d : Fin 2 → Bool) :
    (boolDiagonal d).map star = boolDiagonal d := by
  unfold boolDiagonal
  rw [Matrix.diagonal_map (star_zero ℂ)]
  congr 1
  funext i
  cases d i <;> simp

/-- The first projector selects false lines at the chosen embedding; the
second selects conjugates of true lines at its conjugate embedding. -/
theorem compact_period_selected_lines (σ : E →ₐ[ℚ] ℂ)
    (b : Basis (Fin 2) E (Analysis.DifferentialForms.Coordinates.LocalApproximation.W E)) (d : Fin 2 → Bool) :
    (Analysis.DifferentialForms.Coordinates.LocalApproximation.compactPeriod σ b d).1 * Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix σ b =
      Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix σ b * boolDiagonal (fun i => !d i) ∧
    (Analysis.DifferentialForms.Coordinates.LocalApproximation.compactPeriod σ b d).2 * (Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix σ b).map star =
      (Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix σ b).map star * boolDiagonal d := by
  let M := Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix σ b
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).mp (local_basis_matrix_isUnit σ b)
  have hp : (M * boolDiagonal d * M⁻¹) * M = M * boolDiagonal d := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
  constructor
  · change (1 - M * boolDiagonal d * M⁻¹) * M = M * boolDiagonal (fun i => !d i)
    rw [Matrix.sub_mul, Matrix.one_mul, hp, ← bool_diagonal_complement, Matrix.mul_sub,
      Matrix.mul_one]
  · change (M * boolDiagonal d * M⁻¹).map star * M.map star = M.map star * boolDiagonal d
    calc
      _ = (starRingEnd ℂ).mapMatrix ((M * boolDiagonal d * M⁻¹) * M) :=
        (map_mul (starRingEnd ℂ).mapMatrix _ _).symm
      _ = (starRingEnd ℂ).mapMatrix (M * boolDiagonal d) := congrArg (starRingEnd ℂ).mapMatrix hp
      _ = M.map star * (boolDiagonal d).map star := map_mul (starRingEnd ℂ).mapMatrix _ _
      _ = _ := by rw [conjugate_bool_diagonal]

theorem compact_period_idempotent (σ : E →ₐ[ℚ] ℂ)
    (b : Basis (Fin 2) E (Analysis.DifferentialForms.Coordinates.LocalApproximation.W E)) (d : Fin 2 → Bool) :
    (Analysis.DifferentialForms.Coordinates.LocalApproximation.compactPeriod σ b d).1 * (Analysis.DifferentialForms.Coordinates.LocalApproximation.compactPeriod σ b d).1 = (Analysis.DifferentialForms.Coordinates.LocalApproximation.compactPeriod σ b d).1 ∧
    (Analysis.DifferentialForms.Coordinates.LocalApproximation.compactPeriod σ b d).2 * (Analysis.DifferentialForms.Coordinates.LocalApproximation.compactPeriod σ b d).2 = (Analysis.DifferentialForms.Coordinates.LocalApproximation.compactPeriod σ b d).2 := by
  let M := Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix σ b
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).mp (local_basis_matrix_isUnit σ b)
  have hp : (M * boolDiagonal d * M⁻¹) * (M * boolDiagonal d * M⁻¹) =
      M * boolDiagonal d * M⁻¹ := by
    calc
      _ = M * boolDiagonal d * (M⁻¹ * M) * boolDiagonal d * M⁻¹ := by noncomm_ring
      _ = M * (boolDiagonal d * boolDiagonal d) * M⁻¹ := by
        rw [Matrix.nonsing_inv_mul _ hdet]
        noncomm_ring
      _ = _ := by rw [bool_diagonal_idempotent]
  constructor
  · change (1 - M * boolDiagonal d * M⁻¹) * (1 - M * boolDiagonal d * M⁻¹) =
      1 - M * boolDiagonal d * M⁻¹
    calc
      _ = 1 - M * boolDiagonal d * M⁻¹ - M * boolDiagonal d * M⁻¹ +
          (M * boolDiagonal d * M⁻¹) * (M * boolDiagonal d * M⁻¹) := by noncomm_ring
      _ = _ := by rw [hp]; abel
  · change (M * boolDiagonal d * M⁻¹).map star * (M * boolDiagonal d * M⁻¹).map star =
      (M * boolDiagonal d * M⁻¹).map star
    exact (map_mul (starRingEnd ℂ).mapMatrix _ _).symm.trans
      (congrArg (starRingEnd ℂ).mapMatrix hp)

end

section

/-! ThetaCycle: the actual complex multiplicity-basis change is invertible. -/

open scoped Classical _root_.Matrix
open _root_.Module

variable (K : IntermediateField ℚ ℂ) [IsGalois ℚ K]

def complexTensorBasisEquiv (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K)) :
    ComplexTransition.CM.TotalAmbient K ≃ₗ[ℂ] ComplexTransition.CM.TotalAmbient K :=
  { ComplexTransition.CM.complexTensorBasisChange K b with
    invFun := fun x i τ j =>
      ((Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K τ) b)⁻¹ *ᵥ (fun k => x k τ j)) i
    left_inv := by
      intro x
      funext i τ j
      let M := Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K τ) b
      have hm : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).mp
        (local_basis_matrix_isUnit (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K τ) b)
      change (M⁻¹ *ᵥ (M *ᵥ (fun k => x k τ j))) i = x i τ j
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hm, Matrix.one_mulVec]
    right_inv := by
      intro x
      funext i τ j
      let M := Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K τ) b
      have hm : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).mp
        (local_basis_matrix_isUnit (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K τ) b)
      change (M *ᵥ (M⁻¹ *ᵥ (fun k => x k τ j))) i = x i τ j
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hm, Matrix.one_mulVec] }

theorem complex_tensor_basis_equiv_apply (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K)) (x : ComplexTransition.CM.TotalAmbient K) :
    complexTensorBasisEquiv K b x = ComplexTransition.CM.complexTensorBasisChange K b x := rfl

theorem complex_tensor_basis_change_bijective (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K)) :
    Function.Bijective (ComplexTransition.CM.complexTensorBasisChange K b) :=
  (complexTensorBasisEquiv K b).bijective

end

section

/-! ThetaCycle: explicit holomorphic projectors onto the distinguished line and
its actual bilinear annihilator in the ball prescription. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM _root_.Module

def ballLineProjection (z : HeckeCycles.GeometricSource.CM.BallChart) : HeckeCycles.GeometricSource.CM.Vec ℂ →ₗ[ℂ] HeckeCycles.GeometricSource.CM.Vec ℂ where
  toFun w := w 2 • HeckeCycles.GeometricSource.CM.BallDatum.lineVector z
  map_add' x y := by simp [add_smul]
  map_smul' c w := by
    funext j
    change (c * w 2) * HeckeCycles.GeometricSource.CM.BallDatum.lineVector z j = c * (w 2 * HeckeCycles.GeometricSource.CM.BallDatum.lineVector z j)
    ring

def ballAnnihilatorProjection (β : ℂ) (z : HeckeCycles.GeometricSource.CM.BallChart) : HeckeCycles.GeometricSource.CM.Vec ℂ →ₗ[ℂ] HeckeCycles.GeometricSource.CM.Vec ℂ where
  toFun w := ![w 0, w 1, -(z 0 * w 0 + z 1 * w 1) / β]
  map_add' x y := by
    funext j
    fin_cases j <;> simp [div_eq_mul_inv]
    ring
  map_smul' c w := by
    funext j
    fin_cases j <;> simp [div_eq_mul_inv, smul_eq_mul]
    ring

def ballAnnihilatorEquation (β : ℂ) (z : HeckeCycles.GeometricSource.CM.BallChart) (w : HeckeCycles.GeometricSource.CM.Vec ℂ) : ℂ :=
  z 0 * w 0 + z 1 * w 1 + β * w 2

theorem ball_line_projection_fixed_iff (z : HeckeCycles.GeometricSource.CM.BallChart) (w : HeckeCycles.GeometricSource.CM.Vec ℂ) :
    ballLineProjection z w = w ↔ w ∈ ℂ ∙ HeckeCycles.GeometricSource.CM.BallDatum.lineVector z := by
  constructor
  · intro h
    exact Submodule.mem_span_singleton.mpr ⟨w 2, h⟩
  · intro h
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp h
    simp [ballLineProjection, HeckeCycles.GeometricSource.CM.BallDatum.lineVector]

theorem ball_annihilator_projection_equation (β : ℂ) (hβ : β ≠ 0)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (w : HeckeCycles.GeometricSource.CM.Vec ℂ) :
    ballAnnihilatorEquation β z (ballAnnihilatorProjection β z w) = 0 := by
  change z 0 * w 0 + z 1 * w 1 + β * (-(z 0 * w 0 + z 1 * w 1) / β) = 0
  field_simp [hβ]
  ring

theorem ball_annihilator_projection_fixed_iff (β : ℂ) (hβ : β ≠ 0)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (w : HeckeCycles.GeometricSource.CM.Vec ℂ) :
    ballAnnihilatorProjection β z w = w ↔ ballAnnihilatorEquation β z w = 0 := by
  constructor
  · intro h
    rw [← h]
    exact ball_annihilator_projection_equation β hβ z w
  · intro h
    funext j
    fin_cases j
    · rfl
    · rfl
    · change -(z 0 * w 0 + z 1 * w 1) / β = w 2
      apply (div_eq_iff hβ).mpr
      change z 0 * w 0 + z 1 * w 1 + β * w 2 = 0 at h
      linear_combination -h

theorem ball_line_projection_idempotent (z : HeckeCycles.GeometricSource.CM.BallChart) (w : HeckeCycles.GeometricSource.CM.Vec ℂ) :
    ballLineProjection z (ballLineProjection z w) = ballLineProjection z w := by
  simp [ballLineProjection, HeckeCycles.GeometricSource.CM.BallDatum.lineVector]

theorem ball_annihilator_projection_idempotent (β : ℂ) (z : HeckeCycles.GeometricSource.CM.BallChart) (w : HeckeCycles.GeometricSource.CM.Vec ℂ) :
    ballAnnihilatorProjection β z (ballAnnihilatorProjection β z w) =
      ballAnnihilatorProjection β z w := rfl

theorem ball_line_projection_joint_holomorphic :
    Differentiable ℂ (fun p : HeckeCycles.GeometricSource.CM.BallChart × HeckeCycles.GeometricSource.CM.Vec ℂ => ballLineProjection p.1 p.2) := by
  unfold ballLineProjection
  apply differentiable_pi.mpr
  intro j
  fin_cases j <;> simp [HeckeCycles.GeometricSource.CM.BallDatum.lineVector] <;> fun_prop

theorem ball_annihilator_projection_joint_holomorphic (β : ℂ) :
    Differentiable ℂ (fun p : HeckeCycles.GeometricSource.CM.BallChart × HeckeCycles.GeometricSource.CM.Vec ℂ => ballAnnihilatorProjection β p.1 p.2) := by
  unfold ballAnnihilatorProjection
  apply differentiable_pi.mpr
  intro j
  fin_cases j <;> simp [div_eq_mul_inv] <;> fun_prop

theorem distinguished_local_pairing (K : IntermediateField ℚ ℂ) (β : K)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (w : HeckeCycles.GeometricSource.CM.Vec ℂ) :
    HeckeCycles.GeometricSource.CM.localPairing K β 1 (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z) w = ballAnnihilatorEquation (β : ℂ) z w := by
  simp [HeckeCycles.GeometricSource.CM.localPairing, HeckeCycles.GeometricSource.CM.BallDatum.lineVector, ballAnnihilatorEquation, Fin.sum_univ_succ]
  ring

def distinguishedProjection (K : IntermediateField ℚ ℂ)
    [NumberField K] [NumberField.IsCMField K] (B : HeckeCycles.GeometricSource.CM.BallDatum K) (z : HeckeCycles.GeometricSource.CM.BallChart) :
    (HeckeCycles.GeometricSource.CM.Vec ℂ × HeckeCycles.GeometricSource.CM.Vec ℂ) →ₗ[ℂ] (HeckeCycles.GeometricSource.CM.Vec ℂ × HeckeCycles.GeometricSource.CM.Vec ℂ) :=
  (ballLineProjection z).prodMap (ballAnnihilatorProjection (B.b : ℂ) z)

/-- This is exactly the distinguished-place clause of the accepted HeckeCycles
source prescription, using the actual coefficient of the constructed ball. -/
theorem distinguished_projection_fixed_iff (K : IntermediateField ℚ ℂ)
    [NumberField K] [NumberField.IsCMField K] (B : HeckeCycles.GeometricSource.CM.BallDatum K)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (w : HeckeCycles.GeometricSource.CM.Vec ℂ × HeckeCycles.GeometricSource.CM.Vec ℂ) :
    distinguishedProjection K B z w = w ↔
      w.1 ∈ ℂ ∙ HeckeCycles.GeometricSource.CM.BallDatum.lineVector z ∧ HeckeCycles.GeometricSource.CM.localPairing K B.b 1 (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z) w.2 = 0 := by
  have hβ : (B.b : ℂ) ≠ 0 := by
    intro h
    have hn := B.negative
    rw [h, Complex.zero_re] at hn
    exact (lt_irrefl 0) hn
  change (ballLineProjection z w.1, ballAnnihilatorProjection (B.b : ℂ) z w.2) = w ↔ _
  rw [Prod.ext_iff, ball_line_projection_fixed_iff,
    ball_annihilator_projection_fixed_iff _ hβ, distinguished_local_pairing]

end

/-! ThetaCycle: an actual linear projector onto the full source-prescribed period. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]

def pairedLineProjector (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Gal(K/ℚ) → Bool) (z : HeckeCycles.GeometricSource.CM.BallChart) :
    Lagrangians.CM.pairedAmbient K places →ₗ[ℂ] Lagrangians.CM.pairedAmbient K places where
  toFun w τ := if τ = places.distinguished then distinguishedProjection K B z (w τ)
    else if d (places.representative τ) then (0, (w τ).2) else ((w τ).1, 0)
  map_add' w u := by
    funext τ
    split_ifs <;> simp_all
  map_smul' c w := by
    funext τ
    split_ifs <;> simp_all

theorem paired_line_projector_fixed_iff (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Gal(K/ℚ) → Bool) (z : HeckeCycles.GeometricSource.CM.BallChart) (w : Lagrangians.CM.pairedAmbient K places) :
    pairedLineProjector K B places d z w = w ↔
      HeckeCycles.GeometricSource.CM.prescribed K B places d z ((Symplectic.CM.galoisToPaired K places).symm w) := by
  rw [funext_iff]
  unfold HeckeCycles.GeometricSource.CM.prescribed
  apply forall_congr'
  intro τ
  have hv := Prescribed.CM.paired_inverse_components K places w τ
  have hv₁ := congrArg Prod.fst hv
  have hv₂ := congrArg Prod.snd hv
  change (Symplectic.CM.galoisToPaired K places).symm w (places.representative τ) = (w τ).1 at hv₁
  change (Symplectic.CM.galoisToPaired K places).symm w
    (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * places.representative τ) = (w τ).2 at hv₂
  simp only [pairedLineProjector, LinearMap.coe_mk, AddHom.coe_mk, hv₁, hv₂]
  by_cases hτ : τ = places.distinguished
  · subst τ
    simp only [ite_true, places.identity, distinguished_projection_fixed_iff]
  · cases d (places.representative τ) <;>
      simp [hτ, Prod.ext_iff, eq_comm]

def sourcePeriodProjector (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Gal(K/ℚ) → Bool) (z : HeckeCycles.GeometricSource.CM.BallChart) : HeckeCycles.GeometricSource.CM.Ambient K →ₗ[ℂ] HeckeCycles.GeometricSource.CM.Ambient K :=
  (Symplectic.CM.galoisToPaired K places).symm.toLinearMap.comp <|
    (pairedLineProjector K B places d z).comp (Symplectic.CM.galoisToPaired K places).toLinearMap

theorem source_period_projector_fixed_iff (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Gal(K/ℚ) → Bool) (z : HeckeCycles.GeometricSource.CM.BallChart) (w : HeckeCycles.GeometricSource.CM.Ambient K) :
    sourcePeriodProjector K B places d z w = w ↔ HeckeCycles.GeometricSource.CM.prescribed K B places d z w := by
  rw [← (Symplectic.CM.galoisToPaired K places).injective.eq_iff]
  change Symplectic.CM.galoisToPaired K places ((Symplectic.CM.galoisToPaired K places).symm
    (pairedLineProjector K B places d z (Symplectic.CM.galoisToPaired K places w))) = Symplectic.CM.galoisToPaired K places w ↔ _
  rw [LinearEquiv.apply_symm_apply, paired_line_projector_fixed_iff, LinearEquiv.symm_apply_apply]

omit [IsGalois ℚ K] in
theorem paired_line_projector_idempotent (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Gal(K/ℚ) → Bool) (z : HeckeCycles.GeometricSource.CM.BallChart) (w : Lagrangians.CM.pairedAmbient K places) :
    pairedLineProjector K B places d z (pairedLineProjector K B places d z w) =
      pairedLineProjector K B places d z w := by
  funext τ
  by_cases hτ : τ = places.distinguished
  · simp only [pairedLineProjector, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_left hτ]
    change (ballLineProjection z (ballLineProjection z (w τ).1),
      ballAnnihilatorProjection (B.b : ℂ) z (ballAnnihilatorProjection (B.b : ℂ) z (w τ).2)) = _
    rw [ball_line_projection_idempotent, ball_annihilator_projection_idempotent]
    rfl
  · cases hd : d (places.representative τ) <;> simp [pairedLineProjector, hτ, hd]

theorem source_period_projector_idempotent (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Gal(K/ℚ) → Bool) (z : HeckeCycles.GeometricSource.CM.BallChart) (w : HeckeCycles.GeometricSource.CM.Ambient K) :
    sourcePeriodProjector K B places d z (sourcePeriodProjector K B places d z w) =
      sourcePeriodProjector K B places d z w := by
  simp only [sourcePeriodProjector, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, paired_line_projector_idempotent]

theorem source_period_projector_prescribed (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Gal(K/ℚ) → Bool) (z : HeckeCycles.GeometricSource.CM.BallChart) (w : HeckeCycles.GeometricSource.CM.Ambient K) :
    HeckeCycles.GeometricSource.CM.prescribed K B places d z (sourcePeriodProjector K B places d z w) :=
  (source_period_projector_fixed_iff K B places d z _).mp
    (source_period_projector_idempotent K B places d z w)

theorem source_period_graph_fixed {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Gal(K/ℚ) → Bool}
    (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d) (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ B.domain)
    (x : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    sourcePeriodProjector K B places d z (HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z) x) =
      HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z) x := by
  apply (source_period_projector_fixed_iff K B places d z _).mpr
  apply (L.graph_prescribed z hz _).mpr
  change (L.coordinates.complex (L.coordinates.complex.symm
    ((L.period z).matrix.mulVec x, x))).1 =
      (L.period z).matrix.mulVec
        (L.coordinates.complex (L.coordinates.complex.symm ((L.period z).matrix.mulVec x, x))).2
  rw [LinearEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CompactComplex.CM
