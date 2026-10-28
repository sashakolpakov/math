import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Splitting
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeOrthogonalProduct
import OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionPairing

/-! # Split Inclusions -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.SplitInclusions

noncomputable section

/-! The two coprime factors retain their actual inclusions in the abelian group scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Splitting OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeOrthogonalProduct

attribute [local instance] Kernel.Scheme.kernelGroup

variable {S : Scheme.{u}} {A Z : Over S} [GrpObj A] [GrpObj Z]
  [IsCommMonObj A] [IsCommMonObj Z] (φ : A ⟶ Z) [IsMonHom φ]
  (n d : ℕ) (hnd : n.Coprime d)
  (hk : ∀ (T : Over S) (x : T ⟶ A), x ≫ φ = 1 → x ^ d = 1)

/-- The first factor of the splitting is the original torsion inclusion. -/
theorem first_inclusion :
    CoprimeOrthogonalProduct.first ≫ (Splitting.kernelProductIso φ n d hnd hk).hom ≫ Kernel.Scheme.kernelInclusion (φ ^ n) =
      Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n) := by
  rw [Splitting.kernelProductIso_hom_comp_inclusion, MonObj.comp_mul]
  simp [CoprimeOrthogonalProduct.first]

/-- The second factor of the splitting is the original polarization-kernel inclusion. -/
theorem second_inclusion :
    CoprimeOrthogonalProduct.second ≫ (Splitting.kernelProductIso φ n d hnd hk).hom ≫ Kernel.Scheme.kernelInclusion (φ ^ n) =
      Kernel.Scheme.kernelInclusion φ := by
  rw [Splitting.kernelProductIso_hom_comp_inclusion, MonObj.comp_mul]
  simp [CoprimeOrthogonalProduct.second]

/-- Every scheme-valued point of represented n-torsion is killed by n. -/
theorem torsion_killed (T : Over S) (x : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A) ^ n)) : x ^ n = 1 := by
  apply (cancel_mono (Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n))).mp
  rw [MonObj.pow_comp, MonObj.one_comp]
  have h := (Kernel.Scheme.kernelPointsEquiv ((𝟙 A) ^ n) T x).property
  change (x ≫ Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n)) ≫ (𝟙 A) ^ n = 1 at h
  simpa only [MonObj.comp_pow, Category.comp_id] using h

include hk in
/-- The coprime kernel factor has its given annihilator on all test schemes. -/
theorem kernel_killed (T : Over S) (x : T ⟶ Kernel.Scheme.kernelObject φ) : x ^ d = 1 := by
  apply (cancel_mono (Kernel.Scheme.kernelInclusion φ)).mp
  rw [MonObj.pow_comp, MonObj.one_comp]
  exact hk T _ (Kernel.Scheme.kernelPointsEquiv φ T x).property

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.SplitInclusions
