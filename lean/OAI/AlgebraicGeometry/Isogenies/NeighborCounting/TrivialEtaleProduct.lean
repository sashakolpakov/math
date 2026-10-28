import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleExtremeSubmodules
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupProductFactorMaps

/-! # Trivial Etale Product -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TrivialEtaleProduct

noncomputable section

/-! A product with the literal zero etale subgroup is the original
first factor, through an actual group-scheme isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleExtremeSubmodules

variable {S : Scheme} (M : Grp (Over S)) (G : Type) [Group G] [Subsingleton G]

def trivialEtaleProductIso : M ⊗ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G ≅ M where
  hom := Grp.homMk (fst M.X (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X)
  inv := AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion M (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G)
  hom_inv_id := by
    apply Grp.hom_ext
    change fst M.X (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X ≫
      lift (𝟙 M.X) (1 : M.X ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X) = 𝟙 _
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, lift_snd, MonObj.comp_one, Category.id_comp]
      exact (EtaleExtremeSubmodules.etaleSubsingleton_points G _ (snd M.X (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X)).symm
  inv_hom_id := by
    apply Grp.hom_ext
    exact lift_fst _ _

theorem trivialEtaleProduct_inclusion {E : Grp (Over S)} (i : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G ⟶ E) :
    (trivialEtaleProductIso M G).hom ≫ AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion M E = (𝟙 M) ⊗ₘ i := by
  have hi : i.hom.hom = 1 := by
    have h := EtaleExtremeSubmodules.etaleSubsingleton_points G (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X (𝟙 _)
    exact (Category.id_comp i.hom.hom).symm.trans
      ((congrArg (fun f => f ≫ i.hom.hom) h).trans (MonObj.one_comp i.hom.hom))
  apply Grp.hom_ext
  change fst M.X (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X ≫ lift (𝟙 M.X) (1 : M.X ⟶ E.X) =
    (𝟙 M.X) ⊗ₘ i.hom.hom
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst, Category.comp_id, tensorHom_fst]
  · simp only [Category.assoc, lift_snd, MonObj.comp_one, tensorHom_snd, hi]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TrivialEtaleProduct
