import OAI.RepresentationTheory.Theta.Geometric.SphericalGU

/-! # Lattices -/

namespace OAI.RepresentationTheory.Theta.Geometric.Lattices.Spherical

noncomputable section

/-!
# ElementaryDivisors's determinant adjustment in GeometricTheta's actual local groups

This is the supplied determinant-adjustment proposition applied to the
q-adic integer ring. It constructs an SL3 representative of the same
integral right coset. Inversion gives the manuscript's left-coset and
inverse-lattice convention. No coset-count equality is assumed.
-/

variable (q : ℕ) [Fact q.Prime]

/-- Integral special-linear matrices are exactly the special-linear
matrices whose general-linear images are integral. -/
theorem toGL_integral_iff (g : SphericalGU.Spherical.SL3 q) :
    Matrix.SpecialLinearGroup.toGL g ∈ SphericalGU.Spherical.integralGL3 q ↔ g ∈ SphericalGU.Spherical.integralSL3 q := by
  constructor
  · rintro ⟨U, hU⟩
    have hm : U.val.map (PadicInt.Coe.ringHom (p := q)) = g.val :=
      congrArg Units.val hU
    have hd : U.val.det = 1 := by
      apply Subtype.val_injective
      change PadicInt.Coe.ringHom (p := q) U.val.det = (1 : ℚ_[q])
      rw [RingHom.map_det]
      change (U.val.map (PadicInt.Coe.ringHom (p := q))).det = 1
      rw [hm]
      exact g.property
    let V : Matrix.SpecialLinearGroup (Fin 3) ℤ_[q] := ⟨U.val, hd⟩
    refine ⟨V, ?_⟩
    apply Subtype.ext
    exact hm
  · rintro ⟨U, rfl⟩
    refine ⟨Matrix.SpecialLinearGroup.toGL U, ?_⟩
    apply Units.ext
    rfl

/-- The actual map of integral lattice cosets induced by SL3 into GL3. -/
def specialToGeneralCoset : (SphericalGU.Spherical.SL3 q ⧸ SphericalGU.Spherical.integralSL3 q) → (SphericalGU.Spherical.GL3 q ⧸ SphericalGU.Spherical.integralGL3 q) :=
  Quotient.map Matrix.SpecialLinearGroup.toGL (by
    intro g h hgh
    apply QuotientGroup.leftRel_apply.mpr
    rw [← map_inv, ← map_mul]
    exact (toGL_integral_iff q (g⁻¹ * h)).mpr (QuotientGroup.leftRel_apply.mp hgh))

/-- No special-linear lattice is identified with another by enlarging
the integral group to GL3. This is the injective half of the count comparison. -/
theorem specialToGeneralCoset_injective : Function.Injective (specialToGeneralCoset q) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h g =>
    induction y using Quotient.inductionOn with
    | h h =>
      intro heq
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      apply (toGL_integral_iff q (g⁻¹ * h)).mp
      rw [map_mul, map_inv]
      exact QuotientGroup.eq.mp heq

def DeterminantAdjustment : Prop :=
  ∀ g : SphericalGU.Spherical.GL3 q,
    (∃ u : ℤ_[q]ˣ,
      g.val.det = PadicInt.Coe.ringHom (p := q) (u : ℤ_[q])) →
    ∃ U : Matrix.GeneralLinearGroup (Fin 3) ℤ_[q],
      (g.val * U.val.map (PadicInt.Coe.ringHom (p := q))).det = 1

/-- Construct the special-linear matrix, keeping the integral correction. -/
theorem determinant_one_representative
    (h_ElementaryDivisors : DeterminantAdjustment q)
    (g : SphericalGU.Spherical.GL3 q)
    (hdet : ∃ u : ℤ_[q]ˣ,
      g.val.det = PadicInt.Coe.ringHom (p := q) (u : ℤ_[q])) :
    ∃ s : SphericalGU.Spherical.SL3 q, ∃ U : Matrix.GeneralLinearGroup (Fin 3) ℤ_[q],
      g = Matrix.SpecialLinearGroup.toGL s *
        Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q)) U := by
  obtain ⟨U, hU⟩ := h_ElementaryDivisors g hdet
  let s : SphericalGU.Spherical.SL3 q := ⟨g.val * U.val.map (PadicInt.Coe.ringHom (p := q)), hU⟩
  have hs : Matrix.SpecialLinearGroup.toGL s = g *
      Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q)) U := by
    apply Units.ext
    rfl
  refine ⟨s, U⁻¹, ?_⟩
  rw [hs, map_inv, mul_assoc, mul_inv_cancel, mul_one]

/-- The determinant adjustment preserves the actual lattice coset. -/
theorem determinant_one_same_coset
    (h_ElementaryDivisors : DeterminantAdjustment q)
    (g : SphericalGU.Spherical.GL3 q)
    (hdet : ∃ u : ℤ_[q]ˣ,
      g.val.det = PadicInt.Coe.ringHom (p := q) (u : ℤ_[q])) :
    ∃ s : SphericalGU.Spherical.SL3 q,
      (QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL s) :
        SphericalGU.Spherical.GL3 q ⧸ SphericalGU.Spherical.integralGL3 q) = QuotientGroup.mk g := by
  obtain ⟨s, U, hU⟩ := determinant_one_representative q h_ElementaryDivisors g hdet
  refine ⟨s, QuotientGroup.eq.mpr ?_⟩
  rw [hU, inv_mul_cancel_left]
  exact ⟨U, rfl⟩

/-- The determinant-exponent-zero part of the GL3 lattice quotient. The
condition uses an integral unit determinant of an actual representative. -/
def determinantZeroCosets :=
  {c : SphericalGU.Spherical.GL3 q ⧸ SphericalGU.Spherical.integralGL3 q // ∃ g : SphericalGU.Spherical.GL3 q,
    QuotientGroup.mk g = c ∧ ∃ u : ℤ_[q]ˣ,
      g.val.det = PadicInt.Coe.ringHom (p := q) (u : ℤ_[q])}

def specialToDeterminantZeroCoset (c : SphericalGU.Spherical.SL3 q ⧸ SphericalGU.Spherical.integralSL3 q) :
    determinantZeroCosets q :=
  ⟨specialToGeneralCoset q c, by
    induction c using Quotient.inductionOn with
    | h g =>
      refine ⟨Matrix.SpecialLinearGroup.toGL g, rfl, 1, ?_⟩
      simp⟩

/-- ElementaryDivisors supplies surjectivity onto the determinant-zero lattice cosets;
injectivity was proved directly from the integral matrix embeddings. -/
def determinantZeroCosetEquiv (h_ElementaryDivisors : DeterminantAdjustment q) :
    (SphericalGU.Spherical.SL3 q ⧸ SphericalGU.Spherical.integralSL3 q) ≃ determinantZeroCosets q :=
  Equiv.ofBijective (specialToDeterminantZeroCoset q) ⟨by
    intro c d h
    exact specialToGeneralCoset_injective q (congrArg Subtype.val h), by
    rintro ⟨c, g, hg, hdet⟩
    obtain ⟨s, hs⟩ := determinant_one_same_coset q h_ElementaryDivisors g hdet
    refine ⟨QuotientGroup.mk s, ?_⟩
    apply Subtype.ext
    exact hs.trans hg⟩

@[simp] theorem determinantZeroCosetEquiv_val
    (h_ElementaryDivisors : DeterminantAdjustment q) (c : SphericalGU.Spherical.SL3 q ⧸ SphericalGU.Spherical.integralSL3 q) :
    (determinantZeroCosetEquiv q h_ElementaryDivisors c).val = specialToGeneralCoset q c := rfl

end

end OAI.RepresentationTheory.Theta.Geometric.Lattices.Spherical
