import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange

/-! # Faithful Group Map -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FaithfulGroupMap

noncomputable section

/-! Faithful strong monoidal functors reflect the actual group-homomorphism
laws, as needed after descending an underlying scheme map. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem isMonHom_of_faithful_map
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] [F.Faithful]
    {A B : C} [MonObj A] [MonObj B] (f : A ⟶ B) [IsMonHom (F.map f)] : IsMonHom f where
  one_hom := F.map_injective (by
    simpa [cancel_epi] using IsMonHom.one_hom (F.map f))
  mul_hom := F.map_injective (by
    simpa [cancel_epi] using IsMonHom.mul_hom (F.map f))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FaithfulGroupMap
