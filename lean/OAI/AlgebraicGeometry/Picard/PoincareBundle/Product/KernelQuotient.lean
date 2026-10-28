import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeOrthogonalProduct
import Mathlib.CategoryTheory.EffectiveEpi.Basic

/-! # Kernel Quotient -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.KernelQuotient

noncomputable section

/-! An actual effective quotient of a product by its first factor is the second factor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeOrthogonalProduct

variable {S : Scheme.{u}} {H D E : Over S} [GrpObj H] [GrpObj D] [GrpObj E]
  (r : H ⊗ D ⟶ E) [IsMonHom r]
  (hker : ∀ (T : Over S) (x : T ⟶ H ⊗ D), x ≫ r = 1 ↔ x ≫ snd H D = 1)

include hker

omit [GrpObj H] [IsMonHom r] in
/-- The first factor is killed by the actual quotient morphism. -/
theorem first_killed : CoprimeOrthogonalProduct.first ≫ r = 1 :=
  (hker H CoprimeOrthogonalProduct.first).mpr (by simp [CoprimeOrthogonalProduct.first])

/-- The actual quotient map factors through the second projection by its second-factor restriction. -/
theorem quotient_factorization : snd H D ≫ CoprimeOrthogonalProduct.second ≫ r = r := by
  have hf := congrArg (fun x => x ≫ r) (CoprimeOrthogonalProduct.factors (𝟙 (H ⊗ D)))
  simp only [Category.id_comp, MonObj.mul_comp, Category.assoc, first_killed r hker,
    MonObj.comp_one, one_mul] at hf
  exact hf

/-- The second projection coequalizes every pair identified by the given quotient. -/
theorem projection_coequalizes {T : Over S} (x y : T ⟶ H ⊗ D) (hxy : x ≫ r = y ≫ r) :
    x ≫ snd H D = y ≫ snd H D := by
  have hr : (x / y) ≫ r = 1 := by rw [GrpObj.div_comp, hxy, div_self']
  have hp := (hker T (x / y)).mp hr
  rwa [GrpObj.div_comp, div_eq_one] at hp

variable [EffectiveEpi r]

/-- The inverse to the second-factor map is constructed from the effective quotient. -/
def inverse : E ⟶ D := EffectiveEpi.desc r (snd H D) (projection_coequalizes r hker)

theorem inverse_fac : r ≫ inverse r hker = snd H D :=
  EffectiveEpi.fac r (snd H D) (projection_coequalizes r hker)

/-- The resulting quotient isomorphism is between the actual represented group schemes. -/
def quotientIso : D ≅ E where
  hom := CoprimeOrthogonalProduct.second ≫ r
  inv := inverse r hker
  hom_inv_id := by
    rw [Category.assoc, inverse_fac]
    simp [CoprimeOrthogonalProduct.second]
  inv_hom_id := by
    apply (cancel_epi r).mp
    rw [← Category.assoc, inverse_fac, Category.comp_id]
    exact quotient_factorization r hker

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.KernelQuotient
