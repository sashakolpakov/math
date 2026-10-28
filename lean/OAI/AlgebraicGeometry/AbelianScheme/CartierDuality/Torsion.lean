import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardKernelFiniteness
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FrobeniusReduction
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.TorsionGeometry
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.BaseChange

/-! # Torsion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Torsion.Construction.Multiplication

noncomputable section

/-!
# CartierDuality: torsion finiteness from the actual dual abelian scheme

No integer is required to be invertible on the base. Characteristic-prime
finiteness follows from actual line-bundle descent and dual Frobenius.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

/-- The actual dual Frobenius has finite geometric kernel. -/
theorem finite_dualFrobenius_geometric_kernel
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) :
    Finite (Over.mk (𝟙 (Spec (.of k))) ⟶
      Picard.Homomorphisms.Kernel.Construction.kernelScheme (Picard.Homomorphisms.DualFrobenius.Construction.dualRelativeFrobenius D p Fact.out
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)))) := by
  let hS := Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)
  let F : A.scheme ⟶ (A.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p Fact.out _ hS)).scheme :=
    Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p Fact.out hS A.scheme
  let hF := Picard.Homomorphisms.Quotient.Construction.relativeFrobenius_finiteLocallyFree_quotient p Fact.out hS A.scheme
  have : IsFinite F.left := hF.1.1
  have : Flat F.left := hF.1.2.1
  have : Surjective F.left := hF.2.1
  have : IsMonHom F := Picard.Homomorphisms.Group.Construction.relativeFrobenius_isMonHom p Fact.out hS A.scheme
  exact PicardKernelFiniteness.Construction.KernelCharacters.finite_geometric_dualKernel D
    (D.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p Fact.out _ hS)) F

/-- Characteristic-prime multiplication on the actual dual is finite,
using the represented Picard data and no chosen polarization on the dual. -/
theorem finite_dual_characteristic_power
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) :
    IsFinite ((𝟙 D.abelian.scheme : D.abelian.scheme ⟶ D.abelian.scheme) ^ p).left := by
  have := finite_dualFrobenius_geometric_kernel p k A D
  exact FrobeniusReduction.Construction.Multiplication.finite_dual_characteristic_power_of_finite_dual_kernel p k A D

/-- Every positive multiplication map on the actual dual is finite over
an arbitrary base, without requiring additional duality data for the dual. -/
theorem finite_positive_dual_power
    {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (n : ℕ) (hn : 0 < n) :
    IsFinite ((𝟙 D.abelian.scheme : D.abelian.scheme ⟶ D.abelian.scheme) ^ n).left := by
  apply GeometricFiniteness.Construction.Schemes.finite_positive_powers_of_geometric_characteristic_primes D.abelian.scheme _ n hn
  intro K _ _ a p hp hpK
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := (CharP.charP_iff_prime_eq_zero hp).mpr hpK
  exact finite_dual_characteristic_power p K (A.pullback a) (D.pullback a)

/-- All positive torsion sheaves of the actual dual are finite locally free. -/
theorem dual_torsionFppfAb_finiteLocallyFree
    {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (n : ℕ) (hn : 0 < n) :
    SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S
      (TorsionSheaves.Construction.Schemes.torsionFppfAb (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk D.abelian.scheme)) n) := by
  have := finite_positive_dual_power A D n hn
  exact TorsionGeometry.Construction.Schemes.torsionFppfAb_finiteLocallyFree_of_finite_power (Grp.mk D.abelian.scheme) n

/-- Characteristic-prime multiplication is finite for an abelian variety
admitting an actual isogeny to its actual dual. -/
theorem finite_characteristic_power
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D.abelian) :
    IsFinite ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ p).left := by
  have := finite_dualFrobenius_geometric_kernel p k A D
  exact FrobeniusReduction.Construction.Multiplication.finite_characteristic_power_of_finite_dual_kernel p k A D ell

/-- Every positive multiplication map is finite over an arbitrary base
for abelian schemes with an actual isogeny to their actual dual. -/
theorem finite_positive_power
    {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D.abelian) (n : ℕ) (hn : 0 < n) :
    IsFinite ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left := by
  apply GeometricFiniteness.Construction.Schemes.finite_positive_powers_of_geometric_characteristic_primes A.scheme _ n hn
  intro K _ _ a p hp hpK
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := (CharP.charP_iff_prime_eq_zero hp).mpr hpK
  exact finite_characteristic_power p K (A.pullback a) (D.pullback a) (ell.pullback a)

/-- The actual torsion sheaf is finite locally free for every positive n,
including in residue characteristics dividing n. -/
theorem abelian_torsionFppfAb_finiteLocallyFree
    {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D.abelian) (n : ℕ) (hn : 0 < n) :
    SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S
      (TorsionSheaves.Construction.Schemes.torsionFppfAb (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A.scheme)) n) := by
  have := finite_positive_power A D ell n hn
  exact TorsionGeometry.Construction.Schemes.torsionFppfAb_finiteLocallyFree_of_finite_power (Grp.mk A.scheme) n

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Torsion.Construction.Multiplication
