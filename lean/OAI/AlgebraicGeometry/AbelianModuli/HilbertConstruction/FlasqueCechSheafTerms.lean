import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafSectionCoordinates
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Flasque Cech Sheaf Terms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FlasqueCechSheafTerms.IntrinsicCech

noncomputable section

/-! Products of flasque abelian sheaves and the terms of their Čech resolutions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

variable {X : TopCat.{u}} {ι : Type u}

abbrev evaluateSheaf (V : (Opens X)ᵒᵖ) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat X ⋙ (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj V

def productSectionsIso (F : ι → TopCat.Sheaf AddCommGrpCat.{u} X)
    (V : (Opens X)ᵒᵖ) :
    (∏ᶜ F).obj.obj V ≅ AddCommGrpCat.of (∀ i, (F i).obj.obj V) := by
  letI : PreservesLimitsOfShape (Discrete ι)
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj V) := inferInstance
  letI : PreservesLimit (Discrete.functor F) (evaluateSheaf V) :=
    comp_preservesLimit (TopCat.Sheaf.forget AddCommGrpCat X)
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj V)
  exact PreservesProduct.iso (evaluateSheaf V) F ≪≫
    Additive.GroupProductCoordinates.IntrinsicCech.productIsoPi (fun i => (F i).obj.obj V)

theorem productSectionsIso_apply (F : ι → TopCat.Sheaf AddCommGrpCat.{u} X)
    (V : (Opens X)ᵒᵖ) (x : (∏ᶜ F).obj.obj V) (i : ι) :
    (productSectionsIso F V).hom x i = (Pi.π F i).hom.app V x := by
  change (Additive.GroupProductCoordinates.IntrinsicCech.productIsoPi _).hom
    (piComparison (evaluateSheaf V) F x) i = _
  rw [Additive.GroupProductCoordinates.IntrinsicCech.productIsoPi_hom_apply]
  exact ConcreteCategory.congr_hom (piComparison_comp_π (evaluateSheaf V) F i) x

/-- An arbitrary small product of flasque abelian sheaves is flasque. -/
theorem isFlasque_product (F : ι → TopCat.Sheaf AddCommGrpCat.{u} X)
    [∀ i, TopCat.Sheaf.IsFlasque (F i)] : TopCat.Sheaf.IsFlasque (∏ᶜ F) where
  epi := by
    intro V W f
    rw [AddCommGrpCat.epi_iff_surjective]
    intro x
    have hsurj (i : ι) : Function.Surjective ((F i).obj.map f) :=
      (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
    choose y hy using fun i => hsurj i ((productSectionsIso F W).hom x i)
    refine ⟨(productSectionsIso F V).inv y, ?_⟩
    apply (AddCommGrpCat.mono_iff_injective (productSectionsIso F W).hom).mp
      inferInstance
    funext i
    rw [productSectionsIso_apply]
    have hi := congrArg (fun z => z i) (Iso.inv_hom_id_apply (productSectionsIso F V) y)
    rw [productSectionsIso_apply] at hi
    have hn := ConcreteCategory.congr_hom ((Pi.π F i).hom.naturality f)
      ((productSectionsIso F V).inv y)
    exact hn.trans ((congrArg ((F i).obj.map f) hi).trans (hy i))

/-- Every term of the Čech resolution of a flasque sheaf is flasque. -/
theorem cechTerm_isFlasque (F : TopCat.Sheaf AddCommGrpCat.{u} X) [TopCat.Sheaf.IsFlasque F]
    (U : ι → Opens X) (n : ℕ) : TopCat.Sheaf.IsFlasque (IntrinsicCech.SheafTerms.cechTerm F U n) := by
  have (i : Fin (n + 1) → ι) : TopCat.Sheaf.IsFlasque (IntrinsicCech.SheafTerms.cechTermFactor F U n i) := by
    let V := ∏ᶜ fun k : Fin (n + 1) => U (i k)
    have : TopCat.Sheaf.IsFlasque ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat V.isOpenEmbedding).obj F) :=
      TopologicalSheafRestriction.IntrinsicCech.flasque_of_restrict _ F V.isOpenEmbedding
    exact TopCat.Sheaf.IsFlasque.pushforward_isFlasque _ V.inclusion'
  exact isFlasque_product (IntrinsicCech.SheafTerms.cechTermFactor F U n)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FlasqueCechSheafTerms.IntrinsicCech
