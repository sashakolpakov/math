import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.GroupObjects

/-! # Isogeny Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.IsogenyNaturality

noncomputable section

/-! A commutative square for the forward isogenies also commutes
for their scalar complements. This makes swapping paired quotients
well-defined on isomorphism classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem paired_isogeny_reverse_naturality
    {S : Scheme.{0}} {A B A' B' : Over S} [GrpObj A] [GrpObj A']
    (q : A ⟶ B) (v : B ⟶ A) (q' : A' ⟶ B') (v' : B' ⟶ A')
    [Epi q] (a : A ⟶ A') [IsMonHom a] (b : B ⟶ B') (n : ℕ)
    (h : q ≫ v = (𝟙 A) ^ n) (h' : q' ≫ v' = (𝟙 A') ^ n)
    (hsq : q ≫ b = a ≫ q') : v ≫ a = b ≫ v' := by
  apply (cancel_epi q).mp
  calc
    q ≫ (v ≫ a) = (q ≫ v) ≫ a := (Category.assoc _ _ _).symm
    _ = ((𝟙 A) ^ n) ≫ a := by rw [h]
    _ = a ^ n := by rw [MonObj.pow_comp, Category.id_comp]
    _ = a ≫ ((𝟙 A') ^ n) := by rw [MonObj.comp_pow, Category.comp_id]
    _ = a ≫ (q' ≫ v') := by rw [h']
    _ = q ≫ (b ≫ v') := by rw [← Category.assoc, ← hsq, Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.IsogenyNaturality
