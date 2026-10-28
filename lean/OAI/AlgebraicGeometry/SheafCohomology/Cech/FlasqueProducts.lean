import OAI.AlgebraicGeometry.SheafCohomology.Cech.Terms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Flasque Products -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.FlasqueProducts.TopCat.Sheaf

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

/-! Products of flasque abelian sheaves and the terms of their Čech resolutions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

variable {X : TopCat.{u}} {ι : Type u}

private abbrev evaluateSheaf (V : (Opens X)ᵒᵖ) :
    Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  forget AddCommGrpCat X ⋙ (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj V

set_option backward.isDefEq.respectTransparency false in
private def productSectionsIso (F : ι → Sheaf AddCommGrpCat.{u} X)
    (V : (Opens X)ᵒᵖ) :
    (∏ᶜ F).obj.obj V ≅ AddCommGrpCat.of (∀ i, (F i).obj.obj V) := by
  letI : PreservesLimitsOfShape (Discrete ι)
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj V) := inferInstance
  letI : PreservesLimit (Discrete.functor F) (evaluateSheaf V) :=
    comp_preservesLimit (forget AddCommGrpCat X)
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj V)
  exact asIso (piComparison (evaluateSheaf V) F) ≪≫
    Cochains.AddCommGrpCat.productIsoPi (fun i => (F i).obj.obj V)

private theorem productSectionsIso_apply (F : ι → Sheaf AddCommGrpCat.{u} X)
    (V : (Opens X)ᵒᵖ) (x : (∏ᶜ F).obj.obj V) (i : ι) :
    (productSectionsIso F V).hom x i = (Pi.π F i).hom.app V x := by
  change (Cochains.AddCommGrpCat.productIsoPi _).hom
    (piComparison (evaluateSheaf V) F x) i = _
  rw [Cochains.AddCommGrpCat.productIsoPi_hom_apply]
  exact ConcreteCategory.congr_hom (piComparison_comp_π (evaluateSheaf V) F i) x

/-- An arbitrary small product of flasque abelian sheaves is flasque. -/
theorem isFlasque_product (F : ι → Sheaf AddCommGrpCat.{u} X)
    [∀ i, IsFlasque (F i)] : IsFlasque (∏ᶜ F) where
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
theorem cechTerm_isFlasque (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F]
    (U : ι → Opens X) (n : ℕ) : IsFlasque (Terms.TopCat.Sheaf.cechTerm F U n) := by
  have (i : Fin (n + 1) → ι) : IsFlasque (Terms.TopCat.Sheaf.cechTermFactor F U n i) := by
    let V := ∏ᶜ fun k : Fin (n + 1) => U (i k)
    have : IsFlasque ((TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat V.isOpenEmbedding).obj F) :=
      TopCatRestrict.TopCat.Sheaf.IsFlasque.of_restrict _ F V.isOpenEmbedding
    exact IsFlasque.pushforward_isFlasque _ V.inclusion'
  exact isFlasque_product (Terms.TopCat.Sheaf.cechTermFactor F U n)

end

end OAI.AlgebraicGeometry.SheafCohomology.Cech.FlasqueProducts.TopCat.Sheaf
