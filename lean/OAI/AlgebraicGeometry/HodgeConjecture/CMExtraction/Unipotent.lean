import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TorusCharacters
import OAI.RepresentationTheory.Hecke.CosetCalculusArithmeticMeasure

/-! # Unipotent -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Unipotent.Iwasawa

noncomputable section

/-! Concrete upper-unipotent coordinates and their actual integral
coset fibres, for comparison of finite kernel sums with CosetCalculus integrals. -/

open scoped Classical _root_.Matrix

def gl3Unipotent {R : Type*} [CommRing R] (x y z : R) :
    Matrix.GeneralLinearGroup (Fin 3) R where
  val := !![1, x, y; 0, 1, z; 0, 0, 1]
  inv := !![1, -x, x * z - y; 0, 1, -z; 0, 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    ring
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    ring

theorem gl3Unipotent_mul {R : Type*} [CommRing R] (x y z a b c : R) :
    gl3Unipotent x y z * gl3Unipotent a b c = gl3Unipotent (x + a) (y + b + x * c) (z + c) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gl3Unipotent, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem gl3Unipotent_inv {R : Type*} [CommRing R] (x y z : R) :
    (gl3Unipotent x y z)⁻¹ = gl3Unipotent (-x) (x * z - y) (-z) := by
  apply Units.ext
  rfl

theorem gl3Unipotent_inv_mul {R : Type*} [CommRing R] (x y z a b c : R) :
    (gl3Unipotent x y z)⁻¹ * gl3Unipotent a b c =
      gl3Unipotent (a - x) (b - y - x * (c - z)) (c - z) := by
  rw [gl3Unipotent_inv, gl3Unipotent_mul]
  congr 1 <;> ring

theorem gl3Unipotent_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x y z : R) :
    Matrix.GeneralLinearGroup.map f (gl3Unipotent x y z) = gl3Unipotent (f x) (f y) (f z) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gl3Unipotent, Matrix.GeneralLinearGroup.map]

variable (q : ℕ) [Fact q.Prime]

def padicIntegralSet : Set ℚ_[q] := Set.range (PadicInt.Coe.ringHom (p := q))

theorem gl3Unipotent_integral_iff (x y z : ℚ_[q]) :
    gl3Unipotent x y z ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q ↔
      x ∈ padicIntegralSet q ∧ y ∈ padicIntegralSet q ∧ z ∈ padicIntegralSet q := by
  constructor
  · rintro ⟨U, hU⟩
    exact ⟨⟨U.val 0 1, congrArg (fun g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q => g.val 0 1) hU⟩,
      ⟨U.val 0 2, congrArg (fun g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q => g.val 0 2) hU⟩,
      ⟨U.val 1 2, congrArg (fun g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q => g.val 1 2) hU⟩⟩
  · rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩⟩
    exact ⟨gl3Unipotent a b c, gl3Unipotent_map _ a b c⟩

theorem gl3Unipotent_coset_iff (t : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q) (x y z a b c : ℚ_[q]) :
    (QuotientGroup.mk (t * gl3Unipotent x y z) : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q ⧸ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) =
        QuotientGroup.mk (t * gl3Unipotent a b c) ↔
      a - x ∈ padicIntegralSet q ∧ b - y - x * (c - z) ∈ padicIntegralSet q ∧
        c - z ∈ padicIntegralSet q := by
  rw [QuotientGroup.eq]
  rw [mul_inv_rev, mul_assoc, ← mul_assoc t⁻¹, inv_mul_cancel, one_mul,
    gl3Unipotent_inv_mul, gl3Unipotent_integral_iff]

theorem gl3Unipotent_upper (x y z : ℚ_[q]) :
    gl3Unipotent x y z ∈ RepresentationTheory.Satake.GL3GL.Core.upperBorel ℚ_[q] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [gl3Unipotent]

theorem gl3Torus_mul_unipotent (ell : Fin 3 → ℤ) (x y z : ℚ_[q]) :
    ((AbelianScheme.TateComparison.HeckeKernel.diagonalUnit (fun i => AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ ell i)) *
        gl3Unipotent x y z).val = RepresentationTheory.Hecke.CosetCalculusArithmeticMeasure.triangular (q : ℚ_[q]) ell x y z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AbelianScheme.TateComparison.HeckeKernel.diagonalUnit, AbelianScheme.TateComparison.HeckeKernel.qUnit, gl3Unipotent,
      RepresentationTheory.Hecke.CosetCalculusArithmeticMeasure.triangular, Matrix.diagonal_mul]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Unipotent.Iwasawa
