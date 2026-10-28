import OAI.Algebra.Modules.ElementaryDivisors

/-! # Lattice Bounds -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LatticeBounds.Construction

noncomputable section

/-!
Read lattice inclusions as inequalities on actual Smith exponents. This
fixes the superlattice convention: kernel exponents are the negatives of
the exponents of M in a basis for L.
-/

open _root_.Module
open scoped Pointwise

open OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] {d : ℕ}

def diagonalLattice (π : R) (e : Basis (Fin d) K (Fin d → K)) (a : Fin d → ℤ) :
    Submodule R (Fin d → K) :=
  Submodule.span R (Set.range fun i => (algebraMap R K π) ^ a i • e i)

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem diagonalLattice_eq_powerBasis_span
    (π : R) (hπ : Irreducible π) (e : Basis (Fin d) K (Fin d → K)) (a : Fin d → ℤ) :
    diagonalLattice π e a = Submodule.span R (Set.range (OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.powerBasis π hπ e a)) := by
  unfold diagonalLattice
  congr 1
  apply congrArg Set.range
  funext i
  exact (OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.powerBasis_apply π hπ e a i).symm

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem powerBasis_diagonal_coordinate
    (π : R) (hπ : Irreducible π) (e : Basis (Fin d) K (Fin d → K))
    (a b : Fin d → ℤ) (i : Fin d) :
    (OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.powerBasis π hπ e b).repr ((algebraMap R K π) ^ a i • e i) i =
      (algebraMap R K π) ^ (a i - b i) := by
  simp only [OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.powerBasis_repr, map_smul, Finsupp.smul_apply, Basis.repr_self,
    Finsupp.single_eq_same, smul_eq_mul, mul_one]
  rw [zpow_sub₀ (OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.uniformizer_map_ne_zero hπ), div_eq_mul_inv, mul_comm]

/-- Inclusion of two diagonal DVR lattices is exactly the reverse
coordinatewise ordering of their integer exponents. -/
theorem diagonalLattice_le_iff
    (π : R) (hπ : Irreducible π) (e : Basis (Fin d) K (Fin d → K)) (a b : Fin d → ℤ) :
    diagonalLattice π e a ≤ diagonalLattice π e b ↔ ∀ i, b i ≤ a i := by
  classical
  constructor
  · intro h i
    have hi : (algebraMap R K π) ^ a i • e i ∈ diagonalLattice π e b :=
      h (Submodule.subset_span (Set.mem_range_self i))
    rw [diagonalLattice_eq_powerBasis_span π hπ] at hi
    obtain ⟨r, hr⟩ := ((OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.powerBasis π hπ e b).mem_span_iff_repr_mem R _).mp hi i
    have hint : ∃ r : R, algebraMap R K r = (algebraMap R K π) ^ (a i - b i) :=
      ⟨r, hr.trans (powerBasis_diagonal_coordinate π hπ e a b i)⟩
    exact sub_nonneg.mp ((OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.integral_zpow_iff hπ _).mp hint)
  · intro h
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [diagonalLattice_eq_powerBasis_span π hπ]
    apply ((OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.powerBasis π hπ e b).mem_span_iff_repr_mem R _).mpr
    intro j
    by_cases hji : j = i
    · subst j
      obtain ⟨r, hr⟩ := (OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.integral_zpow_iff (K := K) hπ (a i - b i)).mpr (sub_nonneg.mpr (h i))
      exact ⟨r, hr.trans (powerBasis_diagonal_coordinate π hπ e a b i).symm⟩
    · refine ⟨0, ?_⟩
      simp [OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.powerBasis_repr, Basis.repr_self, hji]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem diagonalLattice_zero (π : R) (e : Basis (Fin d) K (Fin d → K)) :
    diagonalLattice π e (fun _ => 0) = Submodule.span R (Set.range e) := by
  simp [diagonalLattice]

/-- The integral kernel bounds 0 <= -a_i <= h follow exactly from
L <= M <= pi^(-h)L in a simultaneous diagonal basis. -/
theorem superlattice_exponent_bounds
    (π : R) (hπ : Irreducible π) (e : Basis (Fin d) K (Fin d → K))
    (a : Fin d → ℤ) (h : ℕ)
    (hlower : Submodule.span R (Set.range e) ≤ diagonalLattice π e a)
    (hupper : diagonalLattice π e a ≤ diagonalLattice π e (fun _ => -(h : ℤ))) :
    ∀ i, 0 ≤ -a i ∧ -a i ≤ h := by
  have hlow := (diagonalLattice_le_iff π hπ e (fun _ => 0) a).mp
    ((diagonalLattice_zero π e).symm ▸ hlower)
  have hupp := (diagonalLattice_le_iff π hπ e a (fun _ => -(h : ℤ))).mp hupper
  intro i
  have := hlow i
  have := hupp i
  omega

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LatticeBounds.Construction
