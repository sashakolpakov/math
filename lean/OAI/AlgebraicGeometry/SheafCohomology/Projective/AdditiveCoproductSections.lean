import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseGlobalSectionsExact
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoproductMatrixComponents
import Mathlib.Algebra.Category.ModuleCat.Products

/-! # Additive Coproduct Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections

noncomputable section

/-! An additive module-valued functor sends finite coproducts to products of its values. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u v w t

section Category
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable {R : Type w} [Ring R] (F : C ⥤ ModuleCat.{t} R) [F.Additive]
variable {ι : Type} [Fintype ι]

def additiveCoproductIsoPi (M : ι → C) : F.obj (∐ M) ≅ ModuleCat.of R (∀ i, F.obj (M i)) := by
  letI : HasFiniteBiproducts (ModuleCat.{t} R) := HasFiniteBiproducts.of_hasFiniteProducts
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  letI : PreservesBiproductsOfShape ι F :=
    (Functor.preservesFiniteBiproductsOfAdditive F).preserves (J := ι)
  letI : PreservesBiproduct M F := PreservesBiproductsOfShape.preserves (F := F)
  exact F.mapIso (biproduct.isoCoproduct M).symm ≪≫ F.mapBiproduct M ≪≫
    biproduct.isoProduct (F.obj ∘ M) ≪≫ ModuleCat.piIsoPi (F.obj ∘ M)

theorem additiveCoproductIsoPi_hom_projection (M : ι → C) (i : ι) :
    (additiveCoproductIsoPi F M).hom ≫
      ModuleCat.ofHom (LinearMap.proj i : (∀ k, F.obj (M k)) →ₗ[R] F.obj (M i)) =
        F.map (CoproductMatrixComponents.finiteCoproductProjection M i) := by
  simp only [additiveCoproductIsoPi, Iso.trans_hom, Category.assoc,
    ModuleCat.piIsoPi_hom_ker_subtype, biproduct.isoProduct_hom, Pi.lift_comp_π,
    Functor.mapBiproduct_hom]
  erw [biproduct.lift_π]
  exact (F.map_comp _ _).symm

end Category

variable {X S : Scheme.{u}} (π : X ⟶ S)

def baseGlobalSectionsFunctor : X.Modules ⥤ ModuleCat.{u} Γ(S, ⊤) where
  obj M := letI := BaseZeroSections.baseGlobalSectionsModule π M; ModuleCat.of Γ(S, ⊤) Γ(M, ⊤)
  map {M N} f := by
    letI := BaseZeroSections.baseGlobalSectionsModule π M
    letI := BaseZeroSections.baseGlobalSectionsModule π N
    exact ModuleCat.ofHom (BaseGlobalSectionsExact.baseGlobalSectionsMap π f)
  map_id M := by ext; rfl
  map_comp f g := by ext; rfl

instance baseGlobalSectionsFunctor_additive : (baseGlobalSectionsFunctor π).Additive where
  map_add := by intros; ext x; rfl

noncomputable local instance sectionsCoproductBiproducts :
    HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts

def finiteCoproductGlobalSectionsIso {ι : Type} [Fintype ι] (M : ι → X.Modules) :
    (baseGlobalSectionsFunctor π).obj (∐ M) ≅
      ModuleCat.of Γ(S, ⊤) (∀ i, (baseGlobalSectionsFunctor π).obj (M i)) :=
  additiveCoproductIsoPi (baseGlobalSectionsFunctor π) M

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections
