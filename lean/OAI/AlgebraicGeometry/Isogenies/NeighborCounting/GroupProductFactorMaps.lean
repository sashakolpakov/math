import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.AnnihilatorSheaf

/-! # Group Product Factor Maps -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupProductFactorMaps

noncomputable section

/-! Maps out of a product group scheme are determined by their two
actual factor inclusions, on the full functor of test-scheme points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction

variable {S : Scheme} {M E B : Grp (Over S)}

theorem product_factors_identity :
    (show (M ⊗ E).X ⟶ (M ⊗ E).X from fst M.X E.X ≫ (AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion M E).hom.hom) *
      (show (M ⊗ E).X ⟶ (M ⊗ E).X from snd M.X E.X ≫ (AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion M E).hom.hom) =
        𝟙 (M ⊗ E).X := by
  apply CartesianMonoidalCategory.hom_ext
  · change ((fst M.X E.X ≫ lift (𝟙 M.X) (1 : M.X ⟶ E.X)) *
      (snd M.X E.X ≫ lift (1 : E.X ⟶ M.X) (𝟙 E.X))) ≫ fst M.X E.X = _
    simp only [MonObj.mul_comp, Category.assoc, lift_fst, Category.comp_id,
      MonObj.comp_one, mul_one, Category.id_comp]
  · change ((fst M.X E.X ≫ lift (𝟙 M.X) (1 : M.X ⟶ E.X)) *
      (snd M.X E.X ≫ lift (1 : E.X ⟶ M.X) (𝟙 E.X))) ≫ snd M.X E.X = _
    simp only [MonObj.mul_comp, Category.assoc, lift_snd, Category.comp_id,
      MonObj.comp_one, one_mul, Category.id_comp]

theorem product_map_from_factors (f : M ⊗ E ⟶ B) :
    f.hom.hom =
      (fst M.X E.X ≫ (AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion M E ≫ f).hom.hom) *
        (snd M.X E.X ≫ (AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion M E ≫ f).hom.hom) := by
  change f.hom.hom =
    (fst M.X E.X ≫ (AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion M E).hom.hom ≫ f.hom.hom) *
      (snd M.X E.X ≫ (AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion M E).hom.hom ≫ f.hom.hom)
  have h := congrArg (fun u => u ≫ f.hom.hom) (product_factors_identity (M := M) (E := E))
  simpa only [MonObj.mul_comp, Category.assoc, Category.id_comp] using h.symm

theorem group_product_hom_ext (f g : M ⊗ E ⟶ B)
    (hM : AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion M E ≫ f = AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion M E ≫ g)
    (hE : AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion M E ≫ f = AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion M E ≫ g) : f = g := by
  apply Grp.hom_ext
  exact (product_map_from_factors f).trans
    ((congrArg₂ (fun u v => (fst M.X E.X ≫ u.hom.hom) * (snd M.X E.X ≫ v.hom.hom)) hM hE).trans
      (product_map_from_factors g).symm)

theorem splitFirstInclusion_tensorHom {M' E' : Grp (Over S)} (a : M ⟶ M') (b : E ⟶ E') :
    AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion M E ≫ (a ⊗ₘ b) = a ≫ AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion M' E' := by
  apply Grp.hom_ext
  change lift (𝟙 M.X) (1 : M.X ⟶ E.X) ≫ (a.hom.hom ⊗ₘ b.hom.hom) =
    a.hom.hom ≫ lift (𝟙 M'.X) (1 : M'.X ⟶ E'.X)
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, tensorHom_fst, tensorHom_snd, lift_fst_assoc,
      lift_snd_assoc, lift_fst, lift_snd, MonObj.one_comp, MonObj.comp_one,
      Category.id_comp, Category.comp_id]

theorem splitSecondInclusion_tensorHom {M' E' : Grp (Over S)} (a : M ⟶ M') (b : E ⟶ E') :
    AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion M E ≫ (a ⊗ₘ b) = b ≫ AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion M' E' := by
  apply Grp.hom_ext
  change lift (1 : E.X ⟶ M.X) (𝟙 E.X) ≫ (a.hom.hom ⊗ₘ b.hom.hom) =
    b.hom.hom ≫ lift (1 : E'.X ⟶ M'.X) (𝟙 E'.X)
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, tensorHom_fst, tensorHom_snd, lift_fst_assoc,
      lift_snd_assoc, lift_fst, lift_snd, MonObj.one_comp, MonObj.comp_one,
      Category.id_comp, Category.comp_id]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupProductFactorMaps
