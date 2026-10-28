import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DegreeTwoFixedScalars
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.QuaternionNormUniversality
import OAI.Geometry.ComplexBall.Archimedean

/-! # Degree Two Exclusion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Degree two is incompatible with the reference datum's anisotropy.
The original imaginary scalar supplies the quadratic generator, and the
proved rational norm theorem supplies an isotropic vector with last
coordinate one in the original diagonal Hermitian space. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E]

theorem Datum.RankThreePELDatum.not_degree_two {s : ℕ} (P : Datum.RankThreePELDatum E s)
    (hP : P.IsAdmissible) (hdegree : Module.finrank ℚ E = 2) : False := by
  let δ := P.imaginaryScalar
  have hδ0 : δ ≠ 0 := hP.2.2.2.2.2.2.1
  have hδ : NumberField.IsCMField.complexConj E δ = -δ := hP.2.2.2.2.2.2.2.1
  have hδsq : NumberField.IsCMField.complexConj E (δ^2) = δ^2 := by
    rw [map_pow, hδ, neg_sq]
  have hδneg : (P.μ (δ^2)).re < 0 := by
    have he := Geometry.ComplexBall.Archimedean.ArithmeticQuotient.imaginary_embedding_im_sq δ hδ P.μ
    change (P.μ δ).im^2 = -(P.μ (δ^2)).re at he
    have hp := sq_pos_of_ne_zero (Geometry.ComplexBall.Archimedean.ArithmeticQuotient.imaginary_embedding_im_ne_zero δ hδ hδ0 P.μ)
    linarith
  obtain ⟨r, hr, hrE⟩ := DegreeTwoFixedScalars.cmNegativeFixedScalar_isNegativeRational_of_degree_two
    hdegree (δ^2) hδsq P.μ hδneg
  obtain ⟨b, hb, hbE⟩ := P.rational_negative_b_of_degree_two hP hdegree
  obtain ⟨x₁, x₂, y₁, y₂, hn⟩ :=
    QuaternionNormUniversality.PositiveQuaternionNorm.exists_weighted_four_squares (-r) (-b)
      (neg_pos.mpr hr) (neg_pos.mpr hb)
  let f := algebraMap ℚ E
  have hnorm (x y : ℚ) :
      (f x + δ * f y) * NumberField.IsCMField.complexConj E (f x + δ * f y) =
        f (x^2 - r * y^2) := by
    have hx : NumberField.IsCMField.complexConj E (f x) = f x :=
      (NumberField.IsCMField.complexConj E).toRingHom.map_rat_algebraMap x
    have hy : NumberField.IsCMField.complexConj E (f y) = f y :=
      (NumberField.IsCMField.complexConj E).toRingHom.map_rat_algebraMap y
    calc
      _ = (f x)^2 - δ^2 * (f y)^2 := by
        rw [map_add, map_mul, hx, hy, hδ]
        ring
      _ = f (x^2 - r * y^2) := by
        rw [← hrE]
        simp only [map_sub, map_pow, map_mul, f]
  let v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E := ![f x₁ + δ * f y₁, f x₂ + δ * f y₂, 1]
  have hv : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b v v = 0 := by
    have he : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b v v =
        (f x₁ + δ * f y₁) * NumberField.IsCMField.complexConj E (f x₁ + δ * f y₁) +
        (f x₂ + δ * f y₂) * NumberField.IsCMField.complexConj E (f x₂ + δ * f y₂) +
        P.b := by
      simp [NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian, v, Fin.sum_univ_three]
    rw [he, hnorm, hnorm, ← hbE]
    change f (x₁^2 - r * y₁^2) + f (x₂^2 - r * y₂^2) + f b = 0
    rw [← map_add, ← map_add]
    have hn' : (x₁^2 - r * y₁^2) + (x₂^2 - r * y₂^2) + b = 0 := by
      nlinarith [hn]
    rw [hn', map_zero]
  have hz := hP.2.2.2.2.2.1 v hv
  have hlast := congrFun hz (2 : Fin 3)
  change (1 : E) = 0 at hlast
  exact one_ne_zero hlast

theorem Datum.RankThreePELDatum.one_lt_of_admissible {s : ℕ} (P : Datum.RankThreePELDatum E s)
    (hP : P.IsAdmissible) (hdegree : Module.finrank ℚ E = 2 * s) : 1 < s := by
  have hs : 0 < s := (Nat.zero_le P.distinguished.val).trans_lt P.distinguished.isLt
  by_contra hle
  have hs1 : s = 1 := by omega
  exact P.not_degree_two hP (by simpa only [hs1, mul_one] using hdegree)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
