import OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

/-! # Split Unitary -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.SplitUnitary

/-! The actual unitary group over a split quadratic algebra is a general
linear group, obtained by solving the matrix isometry equation in its two
root coordinates. -/

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra

variable {k : Type*} [Field k] [CharZero k] {d : k}
    (r : k) (hr : r ^ 2 = d) (hr0 : r ≠ 0)
    {n : Type*} [Fintype n] [DecidableEq n]

def plusUnits : (Matrix n n (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ →* (Matrix n n k)ˣ :=
  Units.map (SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0).toMonoidHom

def minusUnits : (Matrix n n (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ →* (Matrix n n k)ˣ :=
  Units.map (SpecialUnitary.SplitAlgebra.minusMatrix r hr hr0).toMonoidHom

def transposeUnit (A : (Matrix n n k)ˣ) : (Matrix n n k)ˣ where
  val := A.val.transpose
  inv := A.inv.transpose
  val_inv := by rw [← Matrix.transpose_mul, A.inv_val, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, A.val_inv, Matrix.transpose_one]

omit [CharZero k] in
@[simp] theorem transposeUnit_transposeUnit (A : (Matrix n n k)ˣ) :
    transposeUnit (transposeUnit A) = A := by apply Units.ext; exact Matrix.transpose_transpose _

theorem plusMatrix_conjTranspose (A : Matrix n n (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) :
    SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 A.conjTranspose = (SpecialUnitary.SplitAlgebra.minusMatrix r hr hr0 A).transpose := by
  apply Matrix.ext
  intro i j
  exact SpecialUnitary.SplitAlgebra.plus_star r hr hr0 (A j i)

theorem minusMatrix_conjTranspose (A : Matrix n n (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) :
    SpecialUnitary.SplitAlgebra.minusMatrix r hr hr0 A.conjTranspose = (SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 A).transpose := by
  apply Matrix.ext
  intro i j
  exact SpecialUnitary.SplitAlgebra.minus_star r hr hr0 (A j i)

variable (H : (Matrix n n (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (hH : H.val.conjTranspose = H.val)

include hH in
theorem hermitian_minus : SpecialUnitary.SplitAlgebra.minusMatrix r hr hr0 H.val = (SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 H.val).transpose := by
  rw [← minusMatrix_conjTranspose, hH]

include hH in
theorem unitary_iff_first_equation (g : (Matrix n n (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) :
    g ∈ Weil.AdelicSplitting.UnitaryBase.Construction.unitaryIsometries H.val ↔
      (SpecialUnitary.SplitAlgebra.minusMatrix r hr hr0 g.val).transpose * SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 H.val *
        SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 g.val = SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 H.val := by
  constructor
  · intro hg
    have h := congrArg (SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0) hg
    simpa only [map_mul, plusMatrix_conjTranspose] using h
  · intro hg
    apply SpecialUnitary.SplitAlgebra.matrix_ext_components r hr hr0
    · simpa only [map_mul, plusMatrix_conjTranspose] using hg
    · have h := congrArg Matrix.transpose hg
      simpa only [map_mul, minusMatrix_conjTranspose, hermitian_minus r hr hr0 H hH,
        Matrix.transpose_mul, Matrix.transpose_transpose, mul_assoc] using h

def liftLinear (A : (Matrix n n k)ˣ) : (Matrix n n (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ :=
  SpecialUnitary.SplitAlgebra.joinUnits r hr hr0 A
    (transposeUnit (plusUnits r hr hr0 H * A⁻¹ * (plusUnits r hr hr0 H)⁻¹))

include hH in
theorem liftLinear_unitary (A : (Matrix n n k)ˣ) :
    liftLinear r hr hr0 H A ∈ Weil.AdelicSplitting.UnitaryBase.Construction.unitaryIsometries H.val := by
  apply (unitary_iff_first_equation r hr hr0 H hH _).mpr
  have h : (plusUnits r hr hr0 H * A⁻¹ * (plusUnits r hr hr0 H)⁻¹) *
      plusUnits r hr hr0 H * A = plusUnits r hr hr0 H := by group
  change (SpecialUnitary.SplitAlgebra.minusMatrix r hr hr0 (SpecialUnitary.SplitAlgebra.joinMatrix r hr hr0 A.val
      (transposeUnit (plusUnits r hr hr0 H * A⁻¹ * (plusUnits r hr hr0 H)⁻¹)).val)).transpose *
      SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 H.val * SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0
        (SpecialUnitary.SplitAlgebra.joinMatrix r hr hr0 A.val (transposeUnit
          (plusUnits r hr hr0 H * A⁻¹ * (plusUnits r hr hr0 H)⁻¹)).val) = _
  rw [SpecialUnitary.SplitAlgebra.minusMatrix_join, SpecialUnitary.SplitAlgebra.plusMatrix_join]
  change ((plusUnits r hr hr0 H * A⁻¹ * (plusUnits r hr hr0 H)⁻¹).val.transpose).transpose *
    SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 H.val * A.val = _
  rw [Matrix.transpose_transpose]
  exact congrArg Units.val h

def plusUnitary : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val →* (Matrix n n k)ˣ :=
  (plusUnits r hr hr0).comp (Weil.AdelicSplitting.UnitaryBase.Construction.unitaryIsometries H.val).subtype

include hH in
theorem liftLinear_recovers (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val) :
    liftLinear r hr hr0 H (plusUnitary r hr hr0 H g) = g.val := by
  let A := plusUnits r hr hr0 g.val
  let B := minusUnits r hr hr0 g.val
  let P := plusUnits r hr hr0 H
  have hg : transposeUnit B * P * A = P := by
    apply Units.ext
    exact (unitary_iff_first_equation r hr hr0 H hH g.val).mp g.property
  have hb : transposeUnit B = P * A⁻¹ * P⁻¹ := by
    calc
      transposeUnit B = (transposeUnit B * P * A) * A⁻¹ * P⁻¹ := by group
      _ = P * A⁻¹ * P⁻¹ := by rw [hg]
  have hb' : B = transposeUnit (P * A⁻¹ * P⁻¹) := by
    simpa only [transposeUnit_transposeUnit] using congrArg transposeUnit hb
  apply Units.ext
  apply SpecialUnitary.SplitAlgebra.matrix_ext_components r hr hr0
  · exact SpecialUnitary.SplitAlgebra.plusMatrix_join r hr hr0 _ _
  · rw [liftLinear, SpecialUnitary.SplitAlgebra.joinUnits, SpecialUnitary.SplitAlgebra.minusMatrix_join]
    exact (congrArg Units.val hb').symm

def unitaryEquivGL : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val ≃* (Matrix n n k)ˣ :=
  MulEquiv.ofBijective (plusUnitary r hr hr0 H) ⟨by
    intro g h hgh
    apply Subtype.ext
    rw [← liftLinear_recovers r hr hr0 H hH g, ← liftLinear_recovers r hr hr0 H hH h, hgh], by
    intro A
    refine ⟨⟨liftLinear r hr hr0 H A, liftLinear_unitary r hr hr0 H hH A⟩, ?_⟩
    apply Units.ext
    exact SpecialUnitary.SplitAlgebra.plusMatrix_join r hr hr0 _ _⟩

end RepresentationTheory.Theta.Adelic.SplitUnitary

namespace RepresentationTheory.Theta.Adelic.SplitUnitary.Special

/-! Determinant-one matrices identify the actual special-unitary group of
a split quadratic algebra with SL_n of the base field. -/

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra OAI.RepresentationTheory.Theta.Adelic.SplitUnitary

variable {k : Type*} [Field k] [CharZero k] {d : k}
    (r : k) (hr : r ^ 2 = d) (hr0 : r ≠ 0)
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : (Matrix n n (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (hH : H.val.conjTranspose = H.val)

def plusSpecialUnitary : SpecialUnitary.SU H.val →* Matrix.SpecialLinearGroup n k where
  toFun g := ⟨SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 g.val.val, by
    have hg : g.val.val.det = 1 := congrArg Units.val g.property.2
    change (((SpecialUnitary.SplitAlgebra.plus r hr hr0).mapMatrix) g.val.val).det = 1
    rw [← (SpecialUnitary.SplitAlgebra.plus r hr hr0).map_det, hg, map_one]⟩
  map_one' := by apply Subtype.ext; exact map_one (SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0)
  map_mul' g h := by apply Subtype.ext; exact map_mul (SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0) _ _

theorem liftLinear_det_one (A : (Matrix n n k)ˣ)
    (hA : Matrix.GeneralLinearGroup.det A = 1) :
    Matrix.GeneralLinearGroup.det (liftLinear r hr hr0 H A) = 1 := by
  apply Units.ext
  apply SpecialUnitary.SplitAlgebra.ext_components r hr hr0
  · change SpecialUnitary.SplitAlgebra.plus r hr hr0 (liftLinear r hr hr0 H A).val.det = SpecialUnitary.SplitAlgebra.plus r hr hr0 1
    rw [(SpecialUnitary.SplitAlgebra.plus r hr hr0).map_det, map_one]
    change (SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 (SpecialUnitary.SplitAlgebra.joinMatrix r hr hr0 A.val _)).det = 1
    rw [SpecialUnitary.SplitAlgebra.plusMatrix_join]
    exact congrArg Units.val hA
  · change SpecialUnitary.SplitAlgebra.minus r hr hr0 (liftLinear r hr hr0 H A).val.det = SpecialUnitary.SplitAlgebra.minus r hr hr0 1
    rw [(SpecialUnitary.SplitAlgebra.minus r hr hr0).map_det, map_one]
    change (SpecialUnitary.SplitAlgebra.minusMatrix r hr hr0 (SpecialUnitary.SplitAlgebra.joinMatrix r hr hr0 A.val
      (transposeUnit (plusUnits r hr hr0 H * A⁻¹ * (plusUnits r hr hr0 H)⁻¹)).val)).det = 1
    rw [SpecialUnitary.SplitAlgebra.minusMatrix_join]
    change ((plusUnits r hr hr0 H * A⁻¹ * (plusUnits r hr hr0 H)⁻¹).val.transpose).det = 1
    rw [Matrix.det_transpose]
    have hdet : Matrix.GeneralLinearGroup.det
        (plusUnits r hr hr0 H * A⁻¹ * (plusUnits r hr hr0 H)⁻¹) = 1 := by
      simp [map_mul, map_inv, hA]
    exact congrArg Units.val hdet

def specialUnitaryEquivSL : SpecialUnitary.SU H.val ≃* Matrix.SpecialLinearGroup n k :=
  MulEquiv.ofBijective (plusSpecialUnitary r hr hr0 H) ⟨by
    intro g h hgh
    have he : plusUnitary r hr hr0 H (SpecialUnitary.includeUnitary H.val g) =
        plusUnitary r hr hr0 H (SpecialUnitary.includeUnitary H.val h) :=
      Units.ext (congrArg Subtype.val hgh)
    have hh := (unitaryEquivGL r hr hr0 H hH).injective he
    apply Subtype.ext
    exact congrArg (fun u : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val => u.val) hh, by
    intro A
    refine ⟨⟨liftLinear r hr hr0 H (Matrix.SpecialLinearGroup.toGL A),
      ⟨liftLinear_unitary r hr hr0 H hH _, liftLinear_det_one r hr hr0 H _
        (Matrix.SpecialLinearGroup.coeToGL_det A)⟩⟩, ?_⟩
    apply Subtype.ext
    exact SpecialUnitary.SplitAlgebra.plusMatrix_join r hr hr0 _ _⟩

end RepresentationTheory.Theta.Adelic.SplitUnitary.Special

namespace RepresentationTheory.Theta.Adelic.SplitUnitary.Continuous

/-! Continuity of the explicit root-coordinate map from a split special
unitary group to the actual special linear matrix group. -/

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra OAI.RepresentationTheory.Theta.Adelic.SplitUnitary.Special

variable {k : Type*} [NormedField k] [CharZero k] {d : k}
    (r : k) (hr : r ^ 2 = d) (hr0 : r ≠ 0)
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : (Matrix n n (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)

theorem plus_continuous : Continuous (SpecialUnitary.SplitAlgebra.plus r hr hr0) :=
  (Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_re d).add (continuous_const.mul (Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_im d))

theorem plusSpecialUnitary_continuous : Continuous (Special.plusSpecialUnitary r hr hr0 H) := by
  have hu : Continuous (fun g : SpecialUnitary.SU H.val => (g.val.val : Matrix n n (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))) :=
    Units.continuous_val.comp continuous_subtype_val
  apply continuous_induced_rng.mpr
  change Continuous (fun g : SpecialUnitary.SU H.val => SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 g.val.val)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (plus_continuous r hr hr0).comp
    ((continuous_apply j).comp ((continuous_apply i).comp hu))

def continuousPlusSpecialUnitary : SpecialUnitary.SU H.val →ₜ* Matrix.SpecialLinearGroup n k :=
  { Special.plusSpecialUnitary r hr hr0 H with
    continuous_toFun := plusSpecialUnitary_continuous r hr hr0 H }

end RepresentationTheory.Theta.Adelic.SplitUnitary.Continuous

end

end OAI
