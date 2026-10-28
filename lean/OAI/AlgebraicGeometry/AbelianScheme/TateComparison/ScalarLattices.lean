import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizedComposites
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Lattices
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel

/-! # Scalar Lattices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ScalarLattices

noncomputable section

/-! The actual multiplication map has the inverse-scaled integral
Tate preimage, and scalar elementary divisors determine that lattice. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct Pointwise

universe u
section Tate
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [IsCommMonObj A]
  [GrpObj B] [IsCommMonObj B] (T : Over S) (q : ℕ) [Fact q.Prime]

theorem rationalTateMap_pow (f : A ⟶ B) [IsMonHom f] (n : ℕ) :
    Rational.rationalTateMap (T := T) (q := q) (f ^ n) = n • Rational.rationalTateMap (T := T) (q := q) f := by
  rw [Rational.rationalTateMap, PolarizedComposites.schemeTateMap_pow]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, LinearMap.baseChange_add, ih, succ_nsmul]
    rfl

theorem multiplicationTatePreimage :
    Rational.isogenyTatePreimage (T := T) (q := q) ((𝟙 A) ^ q) =
      (HeckeKernel.qUnit q)⁻¹ • Rational.integralTateImage A T q := by
  ext z
  change Rational.rationalTateMap (T := T) (q := q) ((𝟙 A) ^ q) z ∈ Rational.integralTateImage A T q ↔ _
  rw [rationalTateMap_pow, Functor.rationalTateMap_id]
  change q • z ∈ Rational.integralTateImage A T q ↔ z ∈ (HeckeKernel.qUnit q)⁻¹ • (Rational.integralTateImage A T q : Set _)
  rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
  change q • z ∈ Rational.integralTateImage A T q ↔ (q : ℚ_[q]) • z ∈ Rational.integralTateImage A T q
  rw [Nat.cast_smul_eq_nsmul]

end Tate

section Lattices
variable {R K V W : Type*} [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  [AddCommGroup W] [Module R W] [Module K W] [IsScalarTower R K W]

theorem latticeMap_unit_smul (f : V →ₗ[K] W) (L : Submodule R V) (a : Kˣ) :
    (a • L).map (f.restrictScalars R) = a • L.map (f.restrictScalars R) := by
  ext w
  change (∃ x ∈ a • (L : Set V), f x = w) ↔ w ∈ a • (L.map (f.restrictScalars R) : Set W)
  constructor
  · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨f y, ⟨y, hy, rfl⟩, by exact (f.map_smul (a : K) y).symm⟩
  · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨a • y, ⟨y, hy, rfl⟩, f.map_smul (a : K) y⟩

end Lattices

variable (q : ℕ) [Fact q.Prime]

theorem relativePosition_scalar (L M : Duality.RankThreeLattice ℤ_[q] ℚ_[q])
    (h : Duality.RelativePosition (q : ℤ_[q]) (fun _ => (1 : ℤ)) L M) :
    M.val = (HeckeKernel.qUnit q)⁻¹ • L.val := by
  obtain ⟨b, hL, hM⟩ := h
  rw [hL, hM]
  change Submodule.span ℤ_[q] _ =
    (((HeckeKernel.qUnit q)⁻¹ : ℚ_[q]ˣ) : ℚ_[q]) • Submodule.span ℤ_[q] (Set.range b)
  rw [Submodule.smul_span]
  congr 1
  change Set.range (fun i => (q : ℚ_[q]) ^ (-(1 : ℤ)) • b i) = (HeckeKernel.qUnit q)⁻¹ • Set.range b
  rw [Set.smul_set_range]
  congr 1
  funext i
  simp only [zpow_neg_one]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ScalarLattices
