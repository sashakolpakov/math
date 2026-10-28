import OAI.NumberTheory.Quaternion.Arithmetic.FiniteAdelicLattice
import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.Matrices

/-! # Finite Adelic Eq -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.FiniteAdelicEq

noncomputable section

/-! The inverse image of integral finite-adelic vectors under an
invertible adelic matrix is an actual full finitely generated lattice. -/

open scoped Classical _root_.NumberField
open OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.Matrices.Construction

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem finiteAdelicMatrixLattice_one_eq_standard :
    FiniteAdelicLattice.finiteAdelicMatrixLattice (1 : Matrix (Fin n) (Fin n) (ScalarApproximation.ScalarFiniteAdeles F)) =
      (ArithmeticGroups.Lattices.IntegralLattice.FullLattice.standard F n).module := by
  change _ = Submodule.span (𝓞 F) (Set.range (Pi.basisFun F (Fin n)))
  rw [← ArithmeticGroups.Lattices.Integral.Matrices.Construction.integralCoordinateLattice_eq_span]
  ext x
  rw [FiniteAdelicLattice.mem_finiteAdelicMatrixLattice_one, ArithmeticGroups.Lattices.Integral.Matrices.Construction.mem_integralCoordinateLattice]
  rfl

theorem finiteAdelicMatrixLattice_fg
    (A B : Matrix (Fin n) (Fin n) (ScalarApproximation.ScalarFiniteAdeles F)) (hBA : B * A = 1) :
    (FiniteAdelicLattice.finiteAdelicMatrixLattice A).FG := by
  obtain ⟨d, hd, hclear⟩ := FiniteAdelicLattice.finiteAdelicMatrixLattice_clear_denominators A B hBA
  let f : (Fin n → F) →ₗ[𝓞 F] (Fin n → F) := d • LinearMap.id
  have hinj : Function.Injective f := smul_right_injective (Fin n → F) hd
  apply Submodule.fg_of_fg_map_injective f hinj
  apply (ArithmeticGroups.Lattices.IntegralLattice.FullLattice.standard F n).finite.of_le
  rintro y ⟨x, hx, rfl⟩
  rw [← finiteAdelicMatrixLattice_one_eq_standard]
  exact hclear x hx

theorem finiteAdelicMatrixLattice_full
    (A : Matrix (Fin n) (Fin n) (ScalarApproximation.ScalarFiniteAdeles F)) :
    Submodule.span F (FiniteAdelicLattice.finiteAdelicMatrixLattice A : Set (Fin n → F)) = ⊤ := by
  obtain ⟨d, hd, hinside⟩ := FiniteAdelicLattice.finiteAdelicMatrixLattice_contains_coordinate_multiple A
  have hdF : (d : F) ≠ 0 := by exact_mod_cast hd
  apply top_unique
  rw [← (Pi.basisFun F (Fin n)).span_eq]
  apply Submodule.span_le.mpr
  rintro x ⟨j, rfl⟩
  have hb : Pi.basisFun F (Fin n) j ∈ (ArithmeticGroups.Lattices.IntegralLattice.FullLattice.standard F n).module :=
    Submodule.subset_span (Set.mem_range_self j)
  rw [← finiteAdelicMatrixLattice_one_eq_standard, FiniteAdelicLattice.mem_finiteAdelicMatrixLattice_one] at hb
  have hm := hinside (Pi.basisFun F (Fin n) j) hb
  have hm' : (d : F) • Pi.basisFun F (Fin n) j ∈ FiniteAdelicLattice.finiteAdelicMatrixLattice A := hm
  have h := (Submodule.span F (FiniteAdelicLattice.finiteAdelicMatrixLattice A : Set (Fin n → F))).smul_mem
    ((d : F)⁻¹) (Submodule.subset_span hm')
  rw [smul_smul, inv_mul_cancel₀ hdF, one_smul] at h
  exact h

def finiteAdelicFullLattice (A : (Matrix (Fin n) (Fin n) (ScalarApproximation.ScalarFiniteAdeles F))ˣ) : ArithmeticGroups.Lattices.IntegralLattice.FullLattice F n where
  module := FiniteAdelicLattice.finiteAdelicMatrixLattice A.val
  finite := finiteAdelicMatrixLattice_fg A.val A.inv A.inv_val
  full := finiteAdelicMatrixLattice_full A.val

end

end OAI.NumberTheory.Quaternion.Arithmetic.FiniteAdelicEq
