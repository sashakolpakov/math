import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ScalarLattices

/-! # Power Tate Preimages -/

namespace OAI.RepresentationTheory.Theta.Geometric.PowerTatePreimages

noncomputable section

/-! Exact q-power multiplication scales the actual full and projected
Tate preimages, with the original rational Tate maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj Pointwise

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ScalarLattices

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [IsCommMonObj A]
    [GrpObj B] [IsCommMonObj B] (T : Over S) (q : ℕ) [Fact q.Prime]

theorem powerMultiplicationTatePreimage (n : ℕ) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.isogenyTatePreimage (T := T) (q := q) ((𝟙 A) ^ (q ^ n)) =
      (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ n)⁻¹ • AlgebraicGeometry.AbelianScheme.TateComparison.Rational.integralTateImage A T q := by
  ext z
  change AlgebraicGeometry.AbelianScheme.TateComparison.Rational.rationalTateMap (T := T) (q := q) ((𝟙 A) ^ (q ^ n)) z ∈ AlgebraicGeometry.AbelianScheme.TateComparison.Rational.integralTateImage A T q ↔ _
  rw [AlgebraicGeometry.AbelianScheme.TateComparison.ScalarLattices.rationalTateMap_pow, AlgebraicGeometry.AbelianScheme.TateComparison.Functor.rationalTateMap_id]
  change (q ^ n) • z ∈ AlgebraicGeometry.AbelianScheme.TateComparison.Rational.integralTateImage A T q ↔
    z ∈ (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ n)⁻¹ • (AlgebraicGeometry.AbelianScheme.TateComparison.Rational.integralTateImage A T q : Set _)
  rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
  change (q ^ n) • z ∈ AlgebraicGeometry.AbelianScheme.TateComparison.Rational.integralTateImage A T q ↔ (q : ℚ_[q]) ^ n • z ∈ AlgebraicGeometry.AbelianScheme.TateComparison.Rational.integralTateImage A T q
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

theorem isogenyTatePreimage_congr (f g : A ⟶ B) [IsMonHom f] [IsMonHom g] (h : f = g) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.isogenyTatePreimage (T := T) (q := q) f = AlgebraicGeometry.AbelianScheme.TateComparison.Rational.isogenyTatePreimage (T := T) (q := q) g := by
  subst g
  rfl

variable {T q}

def framedSourceIntegral {s : ℕ} (frame : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateFrame s A T q) (v : Fin s × Bool) :
    Submodule ℤ_[q] (Fin 3 → ℚ_[q]) :=
  (AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedIntegralTateImage frame).map
    ((LinearMap.proj v : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateSpace s q →ₗ[ℚ_[q]] (Fin 3 → ℚ_[q])).restrictScalars ℤ_[q])

theorem framedTateLattice_congr {s : ℕ} (frame : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateFrame s A T q)
    (f g : A ⟶ B) [IsMonHom f] [IsMonHom g] (h : f = g) (v : Fin s × Bool) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice frame f v = AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice frame g v := by
  rw [AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice, AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice, isogenyTatePreimage_congr T q f g h]

theorem powerMultiplication_framedLattice {s : ℕ} (frame : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateFrame s A T q)
    (n : ℕ) (v : Fin s × Bool) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice frame ((𝟙 A) ^ (q ^ n)) v = (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ n)⁻¹ • framedSourceIntegral frame v := by
  rw [AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice, powerMultiplicationTatePreimage, AlgebraicGeometry.AbelianScheme.TateComparison.ScalarLattices.latticeMap_unit_smul, AlgebraicGeometry.AbelianScheme.TateComparison.ScalarLattices.latticeMap_unit_smul]
  rfl

end

end OAI.RepresentationTheory.Theta.Geometric.PowerTatePreimages
