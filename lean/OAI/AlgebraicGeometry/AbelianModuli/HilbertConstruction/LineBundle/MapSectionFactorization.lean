import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionMultiplication
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MonoidalTensorNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Addition

/-! # Map Section Factorization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.MapSectionFactorization

noncomputable section

/-! Tensoring by an invertible sheaf is fully faithful, so every map
from a line bundle to its tensor product with another line bundle is multiplication by a section. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
universe u
local instance lineMapModulesMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules := Module.SheafMonoidal.moduleMonoidalCategory X
local instance lineMapModulesSymmetric (X : Scheme.{u}) : SymmetricCategory X.Modules := Module.SheafMonoidal.moduleSymmetricCategory X
variable {X : Scheme.{u}}

theorem lineBundleMap_exists_multiplying_section (L M : Line.Bundles.LineBundle X)
    (f : M.sheaf ⟶ Tensor.ProductSheaf.tensorModule L.sheaf M.sheaf) :
    ∃ s : Line.Bundles.structureModule X ⟶ L.sheaf, Module.SectionMultiplication.moduleSectionMultiply L M.sheaf s = f := by
  let F := (TensorEquivalence.lineBundleRightTensorEquivalence M).functor
  let e₀ : F.obj (Line.Bundles.structureModule X) ≅ M.sheaf :=
    TensorEquivalence.lineBundleRightTensorEquivalence_objIso M (Line.Bundles.structureModule X) ≪≫ Tensor.ProductSheaf.tensorModuleUnitLeftIso M.sheaf
  let e₁ : F.obj L.sheaf ≅ Tensor.ProductSheaf.tensorModule L.sheaf M.sheaf :=
    TensorEquivalence.lineBundleRightTensorEquivalence_objIso M L.sheaf
  let s := F.preimage (e₀.hom ≫ f ≫ e₁.inv)
  have hs : F.map s = e₀.hom ≫ f ≫ e₁.inv := F.map_preimage _
  refine ⟨s, ?_⟩
  apply (cancel_epi e₀.hom).mp
  calc
    e₀.hom ≫ Module.SectionMultiplication.moduleSectionMultiply L M.sheaf s =
        (TensorEquivalence.lineBundleRightTensorEquivalence_objIso M (Line.Bundles.structureModule X)).hom ≫
          Tensor.Bifunctor.tensorModuleMap s (𝟙 M.sheaf) := by
      simp only [e₀, Iso.trans_hom, Module.SectionMultiplication.moduleSectionMultiply, Category.assoc,
        Iso.hom_inv_id_assoc]
    _ = F.map s ≫ e₁.hom := (Module.MonoidalTensorNaturality.moduleMonoidalTensorIso_natural_left s M.sheaf).symm
    _ = e₀.hom ≫ f := by rw [hs]; simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem tensorPowerMap_exists_multiplying_section (G : Line.Bundles.LineBundle X) (a b : ℕ)
    (f : (G.tensorPower b).sheaf ⟶ (G.tensorPower (a + b)).sheaf) :
    ∃ s : Line.Bundles.structureModule X ⟶ (G.tensorPower a).sheaf,
      Module.SectionMultiplication.moduleSectionMultiply (G.tensorPower a) (G.tensorPower b).sheaf s ≫
        (G.tensorPowerAddIso a b).inv = f := by
  obtain ⟨s, hs⟩ := lineBundleMap_exists_multiplying_section (G.tensorPower a) (G.tensorPower b)
    (f ≫ (G.tensorPowerAddIso a b).hom)
  exact ⟨s, (congrArg (fun q => q ≫ (G.tensorPowerAddIso a b).inv) hs).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun q => f ≫ q) (G.tensorPowerAddIso a b).hom_inv_id).trans
        (Category.comp_id f)))⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.MapSectionFactorization
