import OAI.Analysis.HodgeTheory.Decomposition.ExteriorPair
import OAI.Analysis.HodgeTheory.Decomposition.Pointwise

/-! # Unitary Types -/

namespace OAI.Analysis.HodgeTheory.Decomposition.UnitaryTypes.Constructions

noncomputable section

/-! Separation of bidegrees by unitary tangent scalars, and orthogonality for
the metric on actual alternating covectors. -/

def unitModulusPart (z : ℂˣ) : ℂˣ :=
  Units.mk0 ((‖(z : ℂ)‖⁻¹ : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (inv_ne_zero (norm_ne_zero_iff.mpr z.ne_zero))) * z

theorem unitModulusPart_norm (z : ℂˣ) : ‖(unitModulusPart z : ℂ)‖ = 1 := by
  simp only [unitModulusPart, Units.val_mul, Units.val_mk0, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_inv, abs_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr z.ne_zero)

theorem normalized_bidegreeCharacter {n : ℕ} (i : Core.Constructions.Bidegree n) (z : ℂˣ) :
    DifferentialForms.Manifold.Bidegree.bidegreeCharacter i.val.1 i.val.2 (unitModulusPart z) =
      (((‖(z : ℂ)‖⁻¹ : ℝ) : ℂ) ^ n) * DifferentialForms.Manifold.Bidegree.bidegreeCharacter i.val.1 i.val.2 z := by
  rw [unitModulusPart, DifferentialForms.Manifold.Bidegree.bidegreeCharacter_mul]
  congr 1
  simp only [DifferentialForms.Manifold.Bidegree.bidegreeCharacter, Units.val_mk0, Complex.star_def, Complex.conj_ofReal,
    ← pow_add, i.property]

/-- Distinct bidegrees of the same total degree are distinguished already on the unit circle. -/
theorem exists_unitary_character_separator {n : ℕ} (i j : Core.Constructions.Bidegree n) (hij : i ≠ j) :
    ∃ z : ℂˣ, ‖(z : ℂ)‖ = 1 ∧
      DifferentialForms.Manifold.Bidegree.bidegreeCharacter i.val.1 i.val.2 z ≠ DifferentialForms.Manifold.Bidegree.bidegreeCharacter j.val.1 j.val.2 z := by
  by_contra h
  push Not at h
  have heq (z : ℂˣ) : DifferentialForms.Manifold.Bidegree.bidegreeCharacter i.val.1 i.val.2 z =
      DifferentialForms.Manifold.Bidegree.bidegreeCharacter j.val.1 j.val.2 z := by
    have hz := h (unitModulusPart z) (unitModulusPart_norm z)
    rw [normalized_bidegreeCharacter i z, normalized_bidegreeCharacter j z] at hz
    exact mul_left_cancel₀
      (pow_ne_zero n (Complex.ofReal_ne_zero.mpr
        (inv_ne_zero (norm_ne_zero_iff.mpr z.ne_zero)))) hz
  have hs := Types.Constructions.character_signed_degree i.val.1 i.val.2 j.val.1 j.val.2 heq
  have hi := i.property
  have hj := j.property
  apply hij
  apply Subtype.ext
  apply Prod.ext <;> omega

theorem bidegreeCharacter_norm_one (p q : ℕ) (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1) :
    ‖DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z‖ = 1 := by
  simp [DifferentialForms.Manifold.Bidegree.bidegreeCharacter, norm_pow, hz]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def unitaryScalarIsometry (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1) : E ≃ₗᵢ[ℝ] E where
  toLinearEquiv := (LinearEquiv.smulOfUnit (M := E) z).restrictScalars ℝ
  norm_map' u := by
    change ‖(z : ℂ) • u‖ = ‖u‖
    rw [norm_smul, hz, one_mul]

theorem formMetricPair_unitary (n : ℕ) (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1)
    (f g : DifferentialForms.Manifold.Basic.FormValue E n) :
    ExteriorPair.Constructions.formMetricPair n (DifferentialForms.Manifold.Bidegree.scalarCovectorPullback E n z f) (DifferentialForms.Manifold.Bidegree.scalarCovectorPullback E n z g) =
      ExteriorPair.Constructions.formMetricPair n f g :=
  ExteriorPair.Constructions.formMetricPair_pullback n (unitaryScalarIsometry z hz) f g

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
theorem formMetricPair_smul_left (n : ℕ) (f g : DifferentialForms.Manifold.Basic.FormValue E n) (z : ℂ) :
    ExteriorPair.Constructions.formMetricPair n (z • f) g = star z * ExteriorPair.Constructions.formMetricPair n f g := by
  unfold ExteriorPair.Constructions.formMetricPair CovectorPair.Constructions.covectorInner
  rw [map_smul, CovectorPair.Constructions.covectorBasisPair_smul_left]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
theorem formMetricPair_smul_right (n : ℕ) (f g : DifferentialForms.Manifold.Basic.FormValue E n) (z : ℂ) :
    ExteriorPair.Constructions.formMetricPair n f (z • g) = z * ExteriorPair.Constructions.formMetricPair n f g := by
  rw [← ExteriorPair.Constructions.formMetricPair_symm, formMetricPair_smul_left, star_mul, star_star,
    ExteriorPair.Constructions.formMetricPair_symm, mul_comm]

/-- Distinct pure types are orthogonal for the metric on actual alternating covectors. -/
theorem formMetricPair_pure_orthogonal (n : ℕ) (i j : Core.Constructions.Bidegree n) (hij : i ≠ j)
    (f g : DifferentialForms.Manifold.Basic.FormValue E n) (hf : f.toAlternatingMap ∈ Pointwise.Constructions.algebraicPureSpace E n i)
    (hg : g.toAlternatingMap ∈ Pointwise.Constructions.algebraicPureSpace E n j) : ExteriorPair.Constructions.formMetricPair n f g = 0 := by
  obtain ⟨z, hz, hchars⟩ := exists_unitary_character_separator i j hij
  have hfeq : DifferentialForms.Manifold.Bidegree.scalarCovectorPullback E n z f = DifferentialForms.Manifold.Bidegree.bidegreeCharacter i.val.1 i.val.2 z • f := by
    ext v
    exact hf z v
  have hgeq : DifferentialForms.Manifold.Bidegree.scalarCovectorPullback E n z g = DifferentialForms.Manifold.Bidegree.bidegreeCharacter j.val.1 j.val.2 z • g := by
    ext v
    exact hg z v
  have hp := formMetricPair_unitary n z hz f g
  rw [hfeq, hgeq, formMetricPair_smul_left, formMetricPair_smul_right, ← mul_assoc] at hp
  have hnorm := bidegreeCharacter_norm_one i.val.1 i.val.2 z hz
  have haa : star (DifferentialForms.Manifold.Bidegree.bidegreeCharacter i.val.1 i.val.2 z) *
      DifferentialForms.Manifold.Bidegree.bidegreeCharacter i.val.1 i.val.2 z = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  have hne : star (DifferentialForms.Manifold.Bidegree.bidegreeCharacter i.val.1 i.val.2 z) *
      DifferentialForms.Manifold.Bidegree.bidegreeCharacter j.val.1 j.val.2 z ≠ 1 := by
    intro he
    have hn : star (DifferentialForms.Manifold.Bidegree.bidegreeCharacter i.val.1 i.val.2 z) ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at haa
      exact zero_ne_one haa
    exact hchars (mul_left_cancel₀ hn (haa.trans he.symm))
  have hprod : (star (DifferentialForms.Manifold.Bidegree.bidegreeCharacter i.val.1 i.val.2 z) *
      DifferentialForms.Manifold.Bidegree.bidegreeCharacter j.val.1 j.val.2 z - 1) * ExteriorPair.Constructions.formMetricPair n f g = 0 := by
    rw [sub_mul, hp, one_mul, sub_self]
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)

end

end OAI.Analysis.HodgeTheory.Decomposition.UnitaryTypes.Constructions
