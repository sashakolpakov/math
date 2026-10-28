import OAI.NumberTheory.ArithmeticGroups.Lattices.IntegralLattice

/-! # Matrices -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.Matrices.Construction

noncomputable section

/-! Integral special-linear matrices are exactly the matrices preserving
the standard integral coordinate lattice. -/

open scoped Classical _root_.NumberField
open OAI.NumberTheory.ArithmeticGroups.Lattices.IntegralLattice

def integralCoordinateMap {R k : Type} [CommRing R] [Field k] [Algebra R k] (n : ℕ) :
    (Fin n → R) →ₗ[R] (Fin n → k) :=
  LinearMap.pi fun i => (Algebra.linearMap R k).comp (LinearMap.proj i)

def integralCoordinateLattice {R k : Type} [CommRing R] [Field k] [Algebra R k] (n : ℕ) :
    Submodule R (Fin n → k) := (integralCoordinateMap (R := R) (k := k) n).range

theorem mem_integralCoordinateLattice
    {R k : Type} [CommRing R] [Field k] [Algebra R k] {n : ℕ} (x : Fin n → k) :
    x ∈ integralCoordinateLattice (R := R) n ↔
      ∀ i, ∃ a : R, algebraMap R k a = x i := by
  constructor
  · rintro ⟨a, rfl⟩ i
    exact ⟨a i, rfl⟩
  · intro h
    choose a ha using h
    exact ⟨a, funext ha⟩

theorem integralCoordinateLattice_eq_span
    {R k : Type} [CommRing R] [Field k] [Algebra R k] (n : ℕ) :
    integralCoordinateLattice (R := R) (k := k) n =
      Submodule.span R (Set.range (Pi.basisFun k (Fin n))) := by
  unfold integralCoordinateLattice
  rw [LinearMap.range_eq_map, ← (Pi.basisFun R (Fin n)).span_eq, Submodule.map_span,
    ← Set.range_comp]
  congr 1
  congr 1
  funext j
  ext i
  simp [integralCoordinateMap, Pi.basisFun_apply, Pi.single_apply]

theorem specialLinear_lift_of_integral_entries
    {R k : Type} [CommRing R] [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}
    (g : Algebraic.SL n k) (h : ∀ i j, ∃ a : R, algebraMap R k a = g i j) :
    ∃ A : Matrix.SpecialLinearGroup (Fin n) R,
      Matrix.SpecialLinearGroup.map (algebraMap R k) A = g := by
  choose A hA using h
  let B : Matrix (Fin n) (Fin n) R := Matrix.of A
  have hmap : B.map (algebraMap R k) = (g : Matrix (Fin n) (Fin n) k) := by
    ext i j
    exact hA i j
  have hdet : Matrix.det B = 1 := by
    apply FaithfulSMul.algebraMap_injective R k
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, Matrix.SpecialLinearGroup.det_coe, map_one]
  refine ⟨⟨B, hdet⟩, ?_⟩
  exact Subtype.ext hmap

theorem specialLinear_integralCoordinateLattice_mem
    {R k : Type} [CommRing R] [Field k] [Algebra R k] {n : ℕ}
    (A : Matrix.SpecialLinearGroup (Fin n) R) {x : Fin n → k}
    (hx : x ∈ integralCoordinateLattice (R := R) n) :
    Matrix.SpecialLinearGroup.toLin' (Matrix.SpecialLinearGroup.map (algebraMap R k) A) x ∈
      integralCoordinateLattice (R := R) n := by
  obtain ⟨a, rfl⟩ := hx
  refine ⟨(A : Matrix (Fin n) (Fin n) R).mulVec a, ?_⟩
  ext i
  simp [integralCoordinateMap, Matrix.SpecialLinearGroup.toLin'_apply, Matrix.mulVec,
    dotProduct]

theorem specialLinear_lift_iff_preserves_integral_coordinates
    {R k : Type} [CommRing R] [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}
    (g : Algebraic.SL n k) :
    (∃ A : Matrix.SpecialLinearGroup (Fin n) R,
      Matrix.SpecialLinearGroup.map (algebraMap R k) A = g) ↔
    ∀ x ∈ integralCoordinateLattice (R := R) n,
      Matrix.SpecialLinearGroup.toLin' g x ∈ integralCoordinateLattice (R := R) n := by
  constructor
  · rintro ⟨A, rfl⟩ x hx
    exact specialLinear_integralCoordinateLattice_mem A hx
  · intro h
    apply specialLinear_lift_of_integral_entries g
    intro i j
    have hj : Pi.basisFun k (Fin n) j ∈ integralCoordinateLattice (R := R) n := by
      rw [integralCoordinateLattice_eq_span]
      exact Submodule.subset_span (Set.mem_range_self j)
    have hi := (mem_integralCoordinateLattice _).mp (h _ hj) i
    simpa [Matrix.SpecialLinearGroup.toLin'_apply, Pi.basisFun_apply,
      Matrix.mulVec_single] using hi

theorem specialLinear_integralCoordinateLattice_iff
    {R k : Type} [CommRing R] [Field k] [Algebra R k] {n : ℕ}
    (A : Matrix.SpecialLinearGroup (Fin n) R) (x : Fin n → k) :
    Matrix.SpecialLinearGroup.toLin' (Matrix.SpecialLinearGroup.map (algebraMap R k) A) x ∈
      integralCoordinateLattice (R := R) n ↔ x ∈ integralCoordinateLattice (R := R) n := by
  constructor
  · intro h
    have hi := specialLinear_integralCoordinateLattice_mem A⁻¹ h
    simp only [map_inv] at hi
    change (Matrix.SpecialLinearGroup.toLin'
      (Matrix.SpecialLinearGroup.map (algebraMap R k) A)).symm
        (Matrix.SpecialLinearGroup.toLin'
          (Matrix.SpecialLinearGroup.map (algebraMap R k) A) x) ∈ _ at hi
    simpa only [LinearEquiv.symm_apply_apply] using hi
  · exact specialLinear_integralCoordinateLattice_mem A

theorem standard_lattice_stabilizer_iff_integral
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (g : G.RationalPoints) :
    g ∈ G.latticeStabilizer (IntegralLattice.FullLattice.standard k n) ↔
      ∃ A : Matrix.SpecialLinearGroup (Fin n) (𝓞 k),
        Matrix.SpecialLinearGroup.map (algebraMap (𝓞 k) k) A = g.val := by
  have hΛ : (IntegralLattice.FullLattice.standard k n).module =
      integralCoordinateLattice (R := 𝓞 k) n := (integralCoordinateLattice_eq_span n).symm
  rw [G.mem_latticeStabilizer, hΛ]
  constructor
  · intro h
    exact (specialLinear_lift_iff_preserves_integral_coordinates g.val).mpr
      (fun x hx => (h x).mpr hx)
  · rintro ⟨A, hA⟩ x
    rw [← hA]
    exact specialLinear_integralCoordinateLattice_iff A x

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.Matrices.Construction
