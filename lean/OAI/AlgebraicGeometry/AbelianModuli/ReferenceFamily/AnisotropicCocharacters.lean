import OAI.NumberTheory.Quaternion.Arithmetic.CocharacterWeightMatrices

/-! # Anisotropic Cocharacters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnisotropicCocharacters

noncomputable section

/-! An anisotropic homogeneous quadratic invariant rules out every
nonzero cocharacter weight in the actual faithful representation. -/

theorem double_weight_two_ne_one {F : Type} [Field F] [CharZero F]
    (ν : F →+* ℝ) (z : ℤ) (hz : z ≠ 0) : ((2 : F) ^ z) ^ 2 ≠ 1 := by
  intro h
  have he := congrArg ν h
  simp only [map_pow, map_zpow₀, map_ofNat, map_one] at he
  have hp : (2 : ℝ) ^ (z * 2) = 1 := by
    simpa only [zpow_mul, zpow_ofNat] using he
  have hz0 := (zpow_eq_one_iff_right₀ (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≠ 1)).mp hp
  exact hz (by omega)

variable {F K : Type} [Field F] [CharZero F] [Field K] {n : ℕ}
    (G : NumberTheory.ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ν : F →+* ℝ) (ι : F →+* K)
    (q : (Fin n → F) → K)
    (hq : ∀ a v, q (a • v) = ι a ^ 2 * q v)
    (han : ∀ v, q v = 0 → v = 0)
    (hinv : ∀ (g : G.RationalPoints) v, q (Matrix.SpecialLinearGroup.toLin' g.val v) = q v)

include ν hq han hinv in
theorem cocharacter_nonzero_weight_vanishes (c : G.Cocharacter) (z : ℤ) (hz : z ≠ 0) :
    NumberTheory.Quaternion.Arithmetic.CocharacterWeightMatrices.cocharacterWeightMatrix c z = 0 := by
  let t : Fˣ := Units.mk0 2 (by norm_num)
  let a : F := (t ^ z).val
  have ha : ι a ^ 2 ≠ 1 := by
    intro h
    have h' : a ^ 2 = 1 := ι.injective (by simpa only [map_pow, map_one] using h)
    apply double_weight_two_ne_one ν z hz
    simpa only [a, Units.val_zpow_eq_zpow_val, t, Units.val_mk0] using h'
  have hw := NumberTheory.Quaternion.Arithmetic.CocharacterWeightMatrices.cocharacter_weight_matrix_action c t z
  have hv (j : Fin n) : (fun i => NumberTheory.Quaternion.Arithmetic.CocharacterWeightMatrices.cocharacterWeightMatrix c z i j) = 0 := by
    let v : Fin n → F := fun i => NumberTheory.Quaternion.Arithmetic.CocharacterWeightMatrices.cocharacterWeightMatrix c z i j
    have he : Matrix.SpecialLinearGroup.toLin' (c.hom F (RingHom.id F) t).val v = a • v := by
      funext i
      exact congrArg (fun M : Matrix (Fin n) (Fin n) F => M i j) hw
    have hi := hinv (c.hom F (RingHom.id F) t) v
    rw [he, hq] at hi
    apply han
    by_contra hv0
    exact ha ((mul_eq_right₀ hv0).mp hi)
  apply Matrix.ext
  intro i j
  exact congrFun (hv j) i

include ν hq han hinv in
theorem cocharacter_trivial_of_anisotropic_invariant (c : G.Cocharacter)
    (L : Type) [Field L] (φ : F →+* L) : c.hom L φ = 1 := by
  have hc (i j : Fin n) : NumberTheory.Quaternion.Arithmetic.CocharacterWeightMatrices.cocharacterLaurentMatrix c i j =
      LaurentPolynomial.C ((NumberTheory.Quaternion.Arithmetic.CocharacterWeightMatrices.cocharacterLaurentMatrix c i j).coeff 0) := by
    apply LaurentPolynomial.ext
    intro z
    by_cases hz : z = 0
    · subst z
      simp
    · have hw := congrArg (fun M : Matrix (Fin n) (Fin n) F => M i j)
        (cocharacter_nonzero_weight_vanishes G ν ι q hq han hinv c z hz)
      change (NumberTheory.Quaternion.Arithmetic.CocharacterWeightMatrices.cocharacterLaurentMatrix c i j).coeff z = 0 at hw
      simpa only [LaurentPolynomial.C_apply, ite_eq_right hz] using hw
  apply MonoidHom.ext
  intro t
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  calc
    (c.hom L φ t).val i j = LaurentPolynomial.eval₂ φ t (NumberTheory.Quaternion.Arithmetic.CocharacterWeightMatrices.cocharacterLaurentMatrix c i j) :=
      NumberTheory.ArithmeticGroups.Lattices.Compact.Place.Construction.cocharacter_entry_eq_laurent G c φ t i j
    _ = LaurentPolynomial.eval₂ φ 1 (NumberTheory.Quaternion.Arithmetic.CocharacterWeightMatrices.cocharacterLaurentMatrix c i j) := by
      rw [hc, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_C]
    _ = (c.hom L φ 1).val i j := (NumberTheory.ArithmeticGroups.Lattices.Compact.Place.Construction.cocharacter_entry_eq_laurent G c φ 1 i j).symm
    _ = _ := by rw [map_one]; rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnisotropicCocharacters
