import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitGroupScheme

/-! # Split Hom Ext -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitHomExt.CM

noncomputable section

/-! The two actual factors of a split group object jointly detect group
morphisms. This uses their represented product, on arbitrary test objects. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [BraidedCategory C] [HasPullbacks C]
  {A B D : C} [GrpObj A] [GrpObj B] [GrpObj D]
  [IsCommMonObj A] [IsCommMonObj B]
  (r : A ⟶ B) [IsMonHom r] (s : B ⟶ A) [IsMonHom s] (hrs : s ≫ r = 𝟙 B)

include hrs in
theorem hom_ext (f g : A ⟶ D) [IsMonHom f] [IsMonHom g]
    (hn : Picard.PoincareBundle.Kernel.Scheme.kernelInclusion r ≫ f = Picard.PoincareBundle.Kernel.Scheme.kernelInclusion r ≫ g)
    (he : s ≫ f = s ≫ g) : f = g := by
  apply (cancel_epi (SplitGroupScheme.CM.productIso r s hrs).hom).mp
  rw [SplitGroupScheme.CM.productIso_hom, MonObj.mul_comp, MonObj.mul_comp]
  exact congrArg₂ (· * ·)
    ((Category.assoc _ _ _).trans
      ((congrArg (fst (Picard.PoincareBundle.Kernel.Scheme.kernelObject r) B ≫ ·) hn).trans (Category.assoc _ _ _).symm))
    ((Category.assoc _ _ _).trans
      ((congrArg (snd (Picard.PoincareBundle.Kernel.Scheme.kernelObject r) B ≫ ·) he).trans (Category.assoc _ _ _).symm))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitHomExt.CM
