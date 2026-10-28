import OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.PullbackCancellation
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Splitting

/-! # Descended Scalar Complement -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.DescendedScalarComplement

noncomputable section

/-! Constructing a scalar complement to a homomorphism from its two-sided pullback. -/

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {A B P Q : C} [GrpObj A] [GrpObj B] [GrpObj P] [GrpObj Q]
  (f : A ⟶ B) (m : B ⟶ P) (g : P ⟶ Q) (φ : A ⟶ Q) (t : Q ⟶ A)
  [IsMonHom f] [IsMonHom m] [IsMonHom g] [IsMonHom φ] [IsMonHom t]
  (h : f ≫ m ≫ g = φ) (d : ℕ)
  (ht : φ ≫ t = (𝟙 A) ^ d) (ht' : t ≫ φ = (𝟙 Q) ^ d)

/-- The complement is the original complement conjugated through the quotient and dual quotient. -/
def complement : P ⟶ B := g ≫ t ≫ f

instance complement_isMonHom : IsMonHom (complement f g t) := by
  dsimp [complement]
  infer_instance

include h ht

omit [BraidedCategory C] [GrpObj P] [GrpObj Q] [IsMonHom m] [IsMonHom g] [IsMonHom φ] [IsMonHom t] in
/-- The first complementary identity is detected by the original quotient epimorphism. -/
theorem left_complement [Epi f] : m ≫ complement f g t = (𝟙 B) ^ d := by
  apply (cancel_epi f).mp
  change f ≫ m ≫ g ≫ t ≫ f = f ≫ (𝟙 B) ^ d
  have hh := congrArg (fun z => z ≫ t ≫ f) h
  simp only [Category.assoc] at hh
  rw [hh, ← Category.assoc φ t f, ht, MonObj.pow_comp, MonObj.comp_pow,
    Category.id_comp, Category.comp_id]

omit ht in
omit [IsMonHom φ] in
include ht' in
/-- The other complementary identity follows by scalar cancellation on the actual target group. -/
theorem right_complement [IsCommMonObj P] (v : Q ⟶ P) (n : ℕ)
    (hv : g ≫ v = (𝟙 P) ^ n) [Epi ((𝟙 P) ^ n)] :
    complement f g t ≫ m = (𝟙 P) ^ d := by
  have : IsMonHom ((𝟙 P) ^ d) := Kernel.Splitting.power_isMonHom (𝟙 P) d
  apply Scalar.PullbackCancellation.pullback_injective (𝟙 P) g v n hv
  simp only [Category.id_comp]
  change ((g ≫ t ≫ f) ≫ m) ≫ g = ((𝟙 P) ^ d) ≫ g
  simp only [Category.assoc]
  rw [h, ht',
    MonObj.comp_pow, MonObj.pow_comp, Category.comp_id, Category.id_comp]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.DescendedScalarComplement
