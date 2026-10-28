import OAI.AlgebraicGeometry.FormalGeometry.Completion.Multiplication
import OAI.AlgebraicGeometry.FormalGeometry.Completion.OverEffectiveDescent

/-! # Multiplication Descent -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.MultiplicationDescent.Construction

noncomputable section

/-! Descent through actual multiplication, from vanishing on the actual torsion kernel. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {K : Type u} [Field K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]

omit [IsCommMonObj A] in
/-- Multiplication on the actual product is the product of the multiplication maps. -/
theorem multiplication_tensor (n : ℕ) :
    (𝟙 (A ⊗ A) : A ⊗ A ⟶ A ⊗ A) ^ n =
      ((𝟙 A : A ⟶ A) ^ n) ⊗ₘ ((𝟙 A : A ⟶ A) ^ n) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [MonObj.pow_comp, Category.id_comp, tensorHom_fst,
      MonObj.comp_pow, Category.comp_id]
  · simp only [MonObj.pow_comp, Category.id_comp, tensorHom_snd,
      MonObj.comp_pow, Category.comp_id]

/-- A homomorphism killing the actual torsion kernel is constant on every multiplication fiber. -/
theorem groupHom_equalizes_multiplication
    {B : Over (Spec (CommRingCat.of K))} [GrpObj B]
    (n : ℕ) (f : A ⟶ B) [IsMonHom f]
    (hf : AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n ≫ f = 1)
    (T : Over (Spec (CommRingCat.of K))) (a b : T ⟶ A)
    (hab : a ≫ (𝟙 A : A ⟶ A) ^ n = b ≫ (𝟙 A : A ⟶ A) ^ n) :
    a ≫ f = b ≫ f := by
  have hab' : a ^ n = b ^ n := by
    simpa only [MonObj.comp_pow, Category.comp_id] using hab
  have hk : (a / b) ^ n = 1 := by rw [div_pow, hab', div_self']
  have hkill : (a / b) ≫ f = 1 := by
    rw [← AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι n (a / b) hk, Category.assoc, hf, MonObj.comp_one]
  rw [GrpObj.div_comp] at hkill
  exact div_eq_one.mp hkill

variable [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

/-- Actual fpqc descent constructs the factorization through multiplication by n. -/
theorem groupHom_descends_multiplication
    {B : Over (Spec (CommRingCat.of K))} [GrpObj B]
    (n : ℕ) (hn : (n : K) ≠ 0) (f : A ⟶ B) [IsMonHom f]
    (hf : AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n ≫ f = 1) :
    ∃ g : A ⟶ B, IsMonHom g ∧ ((𝟙 A : A ⟶ A) ^ n) ≫ g = f := by
  let m := (𝟙 A : A ⟶ A) ^ n
  have : IsFinite m.left := Multiplication.Construction.multiplication_isFinite A n hn
  have : Etale m.left := Multiplication.Construction.multiplication_etale A n hn
  have : Surjective m.left := Multiplication.Construction.multiplication_surjective A n hn
  obtain ⟨g, hg, _hu⟩ := OverEffectiveDescent.Construction.over_existsUnique_desc_of_effectiveEpi m f
    (groupHom_equalizes_multiplication A n f hf)
  have : IsProper (A ⊗ A).hom := by dsimp; infer_instance
  have : Smooth (A ⊗ A).hom := by dsimp; infer_instance
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : IsIntegral (A ⊗ A).left := inferInstanceAs (IsIntegral (pullback A.hom A.hom))
  have : IsFinite (m ⊗ₘ m).left := by
    rw [← multiplication_tensor A n]
    exact Multiplication.Construction.multiplication_isFinite (A ⊗ A) n hn
  have : Etale (m ⊗ₘ m).left := by
    rw [← multiplication_tensor A n]
    exact Multiplication.Construction.multiplication_etale (A ⊗ A) n hn
  have : Surjective (m ⊗ₘ m).left := by
    rw [← multiplication_tensor A n]
    exact Multiplication.Construction.multiplication_surjective_of_connected (A ⊗ A) n hn
  have : IsMonHom m := inferInstanceAs (IsMonHom ((𝟙 A : A ⟶ A) ^ n))
  have : Epi (m ⊗ₘ m) := Over.epi_of_epi_left _
  have : IsMonHom g := {
    one_hom := by
      rw [← IsMonHom.one_hom m, Category.assoc, hg, IsMonHom.one_hom f]
    mul_hom := by
      apply (cancel_epi (m ⊗ₘ m)).mp
      rw [← Category.assoc, ← IsMonHom.mul_hom m, Category.assoc, hg,
        IsMonHom.mul_hom f, ← Category.assoc, tensorHom_comp_tensorHom, hg]
  }
  exact ⟨g, inferInstance, hg⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.MultiplicationDescent.Construction
