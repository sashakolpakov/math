import OAI.AlgebraicGeometry.SheafCohomology.Cech.TotalComplexUpNat
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! # Double Complex Signs -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexSigns.DoubleComplex

noncomputable section

/-!
# Signs for first-quadrant cochain total complexes

This supplies the ordinary tensor signs for cochain complexes indexed by the
natural numbers. The first index is horizontal and the second is vertical.
The total complex is mathlib's `HomologicalComplex₂.total`; on its `(p,q)`
summand the differential is the horizontal differential plus `(-1)^p` times
the vertical differential.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Preadditive

/-- The usual tensor signs for nonnegative cochain degrees. -/
instance upNatTensorSigns : ComplexShape.TensorSigns (ComplexShape.up ℕ) :=
  AlgebraicGeometry.SheafCohomology.Cech.TotalComplexUpNat.ComplexShape.upNat_tensorSigns

@[simp]
theorem epsilon_upNat (p : ℕ) :
    (ComplexShape.up ℕ).ε p = (-1 : ℤˣ) ^ p := rfl

@[simp]
theorem pi_upNat (p q : ℕ) :
    ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) (p, q) = p + q := rfl

@[simp]
theorem epsilon1_upNat (p q : ℕ) :
    ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) (p, q) = 1 := rfl

@[simp]
theorem epsilon2_upNat (p q : ℕ) :
    ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) (p, q) = (-1 : ℤˣ) ^ p := rfl

universe u v

variable {R : Type u} [Ring R]
  (K : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

/-- The summands in every total degree have a coproduct in the module category. -/
instance hasTotal : K.HasTotal (ComplexShape.up ℕ) := fun _ => inferInstance

/-- The signed total differential on a summand, with a specified total degree. -/
@[reassoc]
theorem iota_d_of_eq (p q n : ℕ) (h : p + q = n) :
    K.ιTotal (ComplexShape.up ℕ) p q n h ≫
        (K.total (ComplexShape.up ℕ)).d n (n + 1) =
      (K.d p (p + 1)).f q ≫
          K.ιTotal (ComplexShape.up ℕ) (p + 1) q (n + 1) (by
            change p + 1 + q = n + 1
            omega) +
        ((-1 : ℤ) ^ p) • ((K.X p).d q (q + 1) ≫
          K.ιTotal (ComplexShape.up ℕ) p (q + 1) (n + 1) (by
            change p + (q + 1) = n + 1
            omega)) := by
  rw [HomologicalComplex₂.total_d, comp_add, HomologicalComplex₂.ι_D₁,
    HomologicalComplex₂.ι_D₂]
  rw [K.d₁_eq (ComplexShape.up ℕ) (show (ComplexShape.up ℕ).Rel p (p + 1) from rfl)
    q (n + 1) (by change p + 1 + q = n + 1; omega)]
  rw [K.d₂_eq (ComplexShape.up ℕ) p
    (show (ComplexShape.up ℕ).Rel q (q + 1) from rfl)
    (n + 1) (by change p + (q + 1) = n + 1; omega)]
  simp only [epsilon1_upNat, epsilon2_upNat, one_smul, Units.smul_def,
    Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]

/-- On bidegree `(p,q)`, the total differential is `δ + (-1)^p d`. -/
@[reassoc]
theorem iota_d (p q : ℕ) :
    K.ιTotal (ComplexShape.up ℕ) p q (p + q) rfl ≫
        (K.total (ComplexShape.up ℕ)).d (p + q) (p + q + 1) =
      (K.d p (p + 1)).f q ≫
          K.ιTotal (ComplexShape.up ℕ) (p + 1) q (p + q + 1) (by
            change p + 1 + q = p + q + 1
            omega) +
        ((-1 : ℤ) ^ p) • ((K.X p).d q (q + 1) ≫
          K.ιTotal (ComplexShape.up ℕ) p (q + 1) (p + q + 1) (by
            change p + (q + 1) = p + q + 1
            omega)) :=
  iota_d_of_eq K p q (p + q) rfl

end

end OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexSigns.DoubleComplex
