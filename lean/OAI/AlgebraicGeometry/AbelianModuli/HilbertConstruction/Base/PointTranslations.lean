import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionScheme

/-! # Point Translations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Base-valued points act by actual translations of the original abelian scheme. Torsion translations preserve multiplication fibers. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

def Abelian.Schemes.AbelianScheme.basePointTranslation (a : 𝟙_ (Over S) ⟶ A.scheme) : A.scheme ⟶ A.scheme :=
  (toUnit A.scheme ≫ a) * 𝟙 A.scheme

@[simp]
theorem Abelian.Schemes.AbelianScheme.basePointTranslation_one : A.basePointTranslation (1 : 𝟙_ (Over S) ⟶ A.scheme) = 𝟙 A.scheme := by
  simp [Abelian.Schemes.AbelianScheme.basePointTranslation]

theorem Abelian.Schemes.AbelianScheme.basePointTranslation_comp (a b : 𝟙_ (Over S) ⟶ A.scheme) :
    A.basePointTranslation a ≫ A.basePointTranslation b = A.basePointTranslation (a * b) := by
  simp [Abelian.Schemes.AbelianScheme.basePointTranslation, MonObj.comp_mul, mul_left_comm, mul_assoc]

def Abelian.Schemes.AbelianScheme.basePointTranslationIso (a : 𝟙_ (Over S) ⟶ A.scheme) : A.scheme ≅ A.scheme where
  hom := A.basePointTranslation a
  inv := A.basePointTranslation a⁻¹
  hom_inv_id := by rw [Abelian.Schemes.AbelianScheme.basePointTranslation_comp, mul_inv_cancel, Abelian.Schemes.AbelianScheme.basePointTranslation_one]
  inv_hom_id := by rw [Abelian.Schemes.AbelianScheme.basePointTranslation_comp, inv_mul_cancel, Abelian.Schemes.AbelianScheme.basePointTranslation_one]

theorem Abelian.Schemes.AbelianScheme.basePointTranslation_multiplication (N : ℕ) (a : 𝟙_ (Over S) ⟶ A.scheme) (ha : a ^ N = 1) :
    A.basePointTranslation a ≫ A.multiplication N = A.multiplication N := by
  rw [A.comp_multiplication, Abelian.Schemes.AbelianScheme.basePointTranslation, mul_pow, ← MonObj.comp_pow, ha,
    MonObj.comp_one, one_mul]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
