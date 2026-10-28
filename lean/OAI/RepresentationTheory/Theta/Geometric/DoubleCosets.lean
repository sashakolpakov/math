import OAI.Algebra.Modules.ElementaryDivisors
import OAI.RepresentationTheory.Theta.Geometric.Lattices

/-! # Double Cosets -/

namespace OAI.RepresentationTheory.Theta.Geometric.DoubleCosets.Spherical

noncomputable section

section

/-! Instantiate the ElementaryDivisors bridge with the proved DVR theorem. This module
imports no statement stub and adds no determinant-adjustment assumption. -/

variable (q : ℕ) [Fact q.Prime]

theorem padic_determinant_adjustment : Lattices.Spherical.DeterminantAdjustment q := by
  intro g hdet
  exact Algebra.Modules.ElementaryDivisors.gl3_determinant_unit_adjustment
    (R := ℤ_[q]) g hdet

/-- The actual SL3 lattice quotient is the determinant-exponent-zero
part of the GL3 lattice quotient, with the original underlying coset map. -/
def padicDeterminantZeroCosetEquiv :
    (SphericalGU.Spherical.SL3 q ⧸ SphericalGU.Spherical.integralSL3 q) ≃ Lattices.Spherical.determinantZeroCosets q :=
  Lattices.Spherical.determinantZeroCosetEquiv q (padic_determinant_adjustment q)

end

/-! The integral GL3 and SL3 double-coset relations agree on SL3. This is
the Smith-basis step needed before comparing individual Hecke branch counts.
The input is the proved ElementaryDivisors theorem, not an assumed count equality. -/

variable (q : ℕ) [Fact q.Prime]

def InDoubleCoset {G : Type*} [Group G] (K : Subgroup G) (g h : G) : Prop :=
  ∃ u v : K, h = (u : G) * g * (v : G)

private def smithDiagonal (a : Fin 3 → ℤ) : SphericalGU.Spherical.GL3 q :=
  AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.diagonalUnit (fun i => AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ a i)

private theorem smithDiagonal_val (a : Fin 3 → ℤ) :
    (smithDiagonal q a).val = Matrix.diagonal (fun i => (q : ℚ_[q]) ^ a i) := by
  simp [smithDiagonal, AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.diagonalUnit, AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit]

private theorem mapGL_val (U : Matrix.GeneralLinearGroup (Fin 3) ℤ_[q]) :
    (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q)) U).val =
      U.val.map (algebraMap ℤ_[q] ℚ_[q]) := rfl

private theorem special_smith_factors (g : SphericalGU.Spherical.SL3 q) :
    ∃ a : Fin 3 → ℤ, Monotone a ∧ ∑ i, a i = 0 ∧
      ∃ U V : Matrix.SpecialLinearGroup (Fin 3) ℤ_[q],
        Matrix.SpecialLinearGroup.toGL g =
          Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q))
            (Matrix.SpecialLinearGroup.toGL U) * smithDiagonal q a *
          Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q))
            (Matrix.SpecialLinearGroup.toGL V) := by
  obtain ⟨a, ⟨ha, hs, U, V, h⟩, _⟩ :=
    Algebra.Modules.ElementaryDivisors.sl3_smith_normal_form
      (R := ℤ_[q]) (q : ℤ_[q]) PadicInt.irreducible_p g
  refine ⟨a, ha, hs, U, V, ?_⟩
  apply Units.ext
  simpa only [Units.val_mul, smithDiagonal_val, map_natCast,
    mapGL_val,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using h

/-- Enlarging the integral group to GL3 does not merge SL3 double cosets.
Uniqueness of the GL Smith exponents identifies the two SL Smith forms. -/
theorem special_doubleCoset_iff (g h : SphericalGU.Spherical.SL3 q) :
    InDoubleCoset (SphericalGU.Spherical.integralGL3 q) (Matrix.SpecialLinearGroup.toGL g)
      (Matrix.SpecialLinearGroup.toGL h) ↔
    InDoubleCoset (SphericalGU.Spherical.integralSL3 q) g h := by
  constructor
  · rintro ⟨⟨u, U, rfl⟩, ⟨v, V, rfl⟩, hgh⟩
    obtain ⟨a, ha, _, A, B, hg⟩ := special_smith_factors q g
    obtain ⟨b, hb, _, C, D, hh⟩ := special_smith_factors q h
    let m : Matrix.GeneralLinearGroup (Fin 3) ℤ_[q] →* SphericalGU.Spherical.GL3 q :=
      Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q))
    have hab : a = b := by
      obtain ⟨c, _, hc⟩ := Algebra.Modules.ElementaryDivisors.gl3_smith_normal_form
        (R := ℤ_[q]) (q : ℤ_[q]) PadicInt.irreducible_p
        (Matrix.SpecialLinearGroup.toGL h)
      have hga : (Matrix.SpecialLinearGroup.toGL h).val =
          (U * Matrix.SpecialLinearGroup.toGL A).val.map (algebraMap ℤ_[q] ℚ_[q]) *
          Matrix.diagonal (fun i => (algebraMap ℤ_[q] ℚ_[q] (q : ℤ_[q])) ^ a i) *
          (Matrix.SpecialLinearGroup.toGL B * V).val.map (algebraMap ℤ_[q] ℚ_[q]) := by
        have he : Matrix.SpecialLinearGroup.toGL h =
            m (U * Matrix.SpecialLinearGroup.toGL A) * smithDiagonal q a *
              m (Matrix.SpecialLinearGroup.toGL B * V) := by
          rw [map_mul, map_mul, hgh, hg]
          simp only [m, mul_assoc]
        simpa only [m, Units.val_mul, smithDiagonal_val, map_natCast,
          mapGL_val] using congrArg Units.val he
      have hhb : (Matrix.SpecialLinearGroup.toGL h).val =
          C.val.map (algebraMap ℤ_[q] ℚ_[q]) *
          Matrix.diagonal (fun i => (algebraMap ℤ_[q] ℚ_[q] (q : ℤ_[q])) ^ b i) *
          D.val.map (algebraMap ℤ_[q] ℚ_[q]) := by
        simpa only [Units.val_mul, smithDiagonal_val, map_natCast,
          mapGL_val,
          Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using congrArg Units.val hh
      exact (hc a ⟨ha, U * Matrix.SpecialLinearGroup.toGL A,
        Matrix.SpecialLinearGroup.toGL B * V, hga⟩).trans
        (hc b ⟨hb, Matrix.SpecialLinearGroup.toGL C,
          Matrix.SpecialLinearGroup.toGL D, hhb⟩).symm
    subst b
    let sm : Matrix.SpecialLinearGroup (Fin 3) ℤ_[q] →* SphericalGU.Spherical.SL3 q :=
      Matrix.SpecialLinearGroup.map (PadicInt.Coe.ringHom (p := q))
    refine ⟨⟨sm (C * A⁻¹), C * A⁻¹, rfl⟩,
      ⟨sm (B⁻¹ * D), B⁻¹ * D, rfl⟩, ?_⟩
    apply Matrix.SpecialLinearGroup.toGL_injective
    have hcompat (s : Matrix.SpecialLinearGroup (Fin 3) ℤ_[q]) :
        Matrix.SpecialLinearGroup.toGL (sm s) = m (Matrix.SpecialLinearGroup.toGL s) := by
      apply Units.ext
      rfl
    simp only [map_mul, map_inv, hcompat]
    rw [hg, hh]
    simp only [m, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left]
  · rintro ⟨u, v, rfl⟩
    refine ⟨⟨Matrix.SpecialLinearGroup.toGL u.val,
      (Lattices.Spherical.toGL_integral_iff q u.val).mpr u.property⟩,
      ⟨Matrix.SpecialLinearGroup.toGL v.val,
      (Lattices.Spherical.toGL_integral_iff q v.val).mpr v.property⟩, ?_⟩
    simp only [map_mul]

/-- Actual integral right cosets contained in one double coset. Inversion
identifies these with the manuscript's left-coset branch convention. -/
def DoubleCosetFiber {G : Type*} [Group G] (K : Subgroup G) (g : G) :=
  {c : G ⧸ K // ∃ h : G, QuotientGroup.mk h = c ∧ InDoubleCoset K g h}

def specialDoubleCosetMap (g : SphericalGU.Spherical.SL3 q)
    (c : DoubleCosetFiber (SphericalGU.Spherical.integralSL3 q) g) :
    DoubleCosetFiber (SphericalGU.Spherical.integralGL3 q) (Matrix.SpecialLinearGroup.toGL g) :=
  ⟨Lattices.Spherical.specialToGeneralCoset q c.val, by
    obtain ⟨h, hh, hcos⟩ := c.property
    refine ⟨Matrix.SpecialLinearGroup.toGL h, ?_,
      (special_doubleCoset_iff q g h).mpr hcos⟩
    rw [← hh]
    rfl⟩

private theorem unitDet_of_special_doubleCoset (g : SphericalGU.Spherical.SL3 q) (h : SphericalGU.Spherical.GL3 q)
    (hcos : InDoubleCoset (SphericalGU.Spherical.integralGL3 q) (Matrix.SpecialLinearGroup.toGL g) h) :
    ∃ u : ℤ_[q]ˣ, h.val.det = PadicInt.Coe.ringHom (p := q) (u : ℤ_[q]) := by
  obtain ⟨⟨u, U, rfl⟩, ⟨v, V, rfl⟩, rfl⟩ := hcos
  refine ⟨U.det * V.det, ?_⟩
  simp [Units.val_mul, Matrix.det_mul,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, RingHom.map_det,
    Matrix.GeneralLinearGroup.val_det_apply]

/-- The bijection preserves each individual double coset, proving the
branch-count comparison, not just an equivalence of the whole quotients. -/
def specialDoubleCosetEquiv (g : SphericalGU.Spherical.SL3 q) :
    DoubleCosetFiber (SphericalGU.Spherical.integralSL3 q) g ≃
      DoubleCosetFiber (SphericalGU.Spherical.integralGL3 q) (Matrix.SpecialLinearGroup.toGL g) :=
  Equiv.ofBijective (specialDoubleCosetMap q g) ⟨by
    intro c d h
    apply Subtype.ext
    exact Lattices.Spherical.specialToGeneralCoset_injective q (congrArg Subtype.val h), by
    rintro ⟨c, h, hh, hcos⟩
    obtain ⟨s, hs⟩ := Lattices.Spherical.determinant_one_same_coset q (padic_determinant_adjustment q)
      h (unitDet_of_special_doubleCoset q g h hcos)
    have hsclass : InDoubleCoset (SphericalGU.Spherical.integralGL3 q) (Matrix.SpecialLinearGroup.toGL g)
        (Matrix.SpecialLinearGroup.toGL s) := by
      obtain ⟨u, v, hv⟩ := hcos
      let k : SphericalGU.Spherical.integralGL3 q := ⟨(Matrix.SpecialLinearGroup.toGL s)⁻¹ * h,
        QuotientGroup.eq.mp hs⟩
      refine ⟨u, v * k⁻¹, ?_⟩
      change Matrix.SpecialLinearGroup.toGL s = u.val *
        Matrix.SpecialLinearGroup.toGL g * (v.val * ((Matrix.SpecialLinearGroup.toGL s)⁻¹ * h)⁻¹)
      rw [← mul_assoc, ← hv]
      simp only [mul_inv_rev, inv_inv, mul_inv_cancel_left]
    refine ⟨⟨QuotientGroup.mk s, s, rfl,
      (special_doubleCoset_iff q g s).mp hsclass⟩, ?_⟩
    apply Subtype.ext
    exact hs.trans hh⟩

theorem special_doubleCoset_count (g : SphericalGU.Spherical.SL3 q) :
    Nat.card (DoubleCosetFiber (SphericalGU.Spherical.integralSL3 q) g) =
      Nat.card (DoubleCosetFiber (SphericalGU.Spherical.integralGL3 q) (Matrix.SpecialLinearGroup.toGL g)) :=
  Nat.card_congr (specialDoubleCosetEquiv q g)

end

end OAI.RepresentationTheory.Theta.Geometric.DoubleCosets.Spherical
