import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TestLineTriviality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ParameterLineKernel

/-! # Biextension Translation Line Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionTranslationLineKernel

noncomputable section

/-! An actual Poincare tensor formula identifies infinitesimal
translation of the original line bundle with its parameter-family
Picard kernel element. The factor from the dual test is proved trivial. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Quotients.FiniteDescent.LineBundleDual.Construction.LineBundlePicard.instCommGroupIsoClass

variable (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) [GrpObj G] (L : HilbertConstruction.Line.Bundles.LineBundle G.left) (Q : HilbertConstruction.Line.Bundles.LineBundle (G ⊗ G).left)

theorem biextension_dualTranslation_class
    (e : ((Q.tensor (L.pullback (fst G G).left)).tensor (L.pullback (snd G G).left)).sheaf ≅
      (L.pullback (MonObj.mul (X := G)).left).sheaf)
    (t : DualOpen.Lifts.DualSchemePoints G 1) :
    RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass Q t.val * HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd (LieRanks.dualNumberTest ℂ) G).left) =
      HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation G t).left) := by
  let j := t.val ⊗ₘ 𝟙 G
  have hj₁ : j ≫ fst G G = fst (LieRanks.dualNumberTest ℂ) G ≫ t.val := tensorHom_fst _ _
  have hj₂ : j ≫ snd G G = snd (LieRanks.dualNumberTest ℂ) G := (tensorHom_snd _ _).trans (Category.comp_id _)
  have hjm : j ≫ MonObj.mul (X := G) = Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation G t := by
    rw [MonObj.mul_eq_mul, MonObj.comp_mul, hj₁, hj₂]
    rfl
  have h₀ : HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback t.val.left) = 1 := Quotient.sound (Dual.TestLineTriviality.dualNumberTestLine_trivial _)
  have h₁ : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass j.left (HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (fst G G).left)) = 1 := by
    change HilbertConstruction.Line.Bundles.LineBundle.pullbackClass j.left (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (fst G G).left (HilbertConstruction.Line.Bundles.LineBundle.classOf L)) = 1
    rw [← HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, show j.left ≫ (fst G G).left =
      (fst (LieRanks.dualNumberTest ℂ) G).left ≫ t.val.left from congrArg Over.Hom.left hj₁,
      HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
    exact (congrArg (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (fst (LieRanks.dualNumberTest ℂ) G).left) h₀).trans
      (map_one (HilbertConstruction.Line.Bundles.LineBundle.pullbackClassMonoidHom (fst (LieRanks.dualNumberTest ℂ) G).left))
  have h₂ : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass j.left (HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd G G).left)) =
      HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd (LieRanks.dualNumberTest ℂ) G).left) := by
    exact (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp j.left (snd G G).left (HilbertConstruction.Line.Bundles.LineBundle.classOf L)).symm.trans
      (congrArg (fun a => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass a (HilbertConstruction.Line.Bundles.LineBundle.classOf L)) (congrArg Over.Hom.left hj₂))
  have hm : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass j.left (HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (MonObj.mul (X := G)).left)) =
      HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation G t).left) :=
    (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp j.left (MonObj.mul (X := G)).left (HilbertConstruction.Line.Bundles.LineBundle.classOf L)).symm.trans
      (congrArg (fun a => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass a (HilbertConstruction.Line.Bundles.LineBundle.classOf L)) (congrArg Over.Hom.left hjm))
  have he : (HilbertConstruction.Line.Bundles.LineBundle.classOf Q * HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (fst G G).left)) *
      HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd G G).left) = HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (MonObj.mul (X := G)).left) :=
    Quotient.sound ⟨e⟩
  have h := congrArg (HilbertConstruction.Line.Bundles.LineBundle.pullbackClassMonoidHom j.left) he
  rw [map_mul, map_mul] at h
  change (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass j.left (HilbertConstruction.Line.Bundles.LineBundle.classOf Q) *
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass j.left (HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (fst G G).left))) *
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass j.left (HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd G G).left)) =
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass j.left (HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (MonObj.mul (X := G)).left)) at h
  rw [h₁, h₂, hm, mul_one] at h
  exact h

theorem dualTranslationLineKernel_biextension
    (e₀ : (Q.pullback (lift (1 : G ⟶ G) (𝟙 G)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule G.left)
    (e : ((Q.tensor (L.pullback (fst G G).left)).tensor (L.pullback (snd G G).left)).sheaf ≅
      (L.pullback (MonObj.mul (X := G)).left).sheaf)
    (t : DualOpen.Lifts.DualSchemePoints G 1) : Intrinsic.InfinitesimalTranslation.dualTranslationLineKernel G L t = Dual.ParameterLineKernel.dualParameterLineKernel Q e₀ t := by
  apply Subtype.ext
  let : CommGroup (HilbertConstruction.Line.Bundles.LineBundle.IsoClass (LieRanks.dualNumberTest ℂ ⊗ G).left) :=
    Quotients.FiniteDescent.LineBundleDual.Construction.LineBundlePicard.instCommGroupIsoClass
  calc
    _ = HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation G t).left) /
        HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd (LieRanks.dualNumberTest ℂ) G).left) :=
      DualLine.PullbackDifference.dualLinePullbackDifferenceKernel_class G (Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation G t).left
        (snd (LieRanks.dualNumberTest ℂ) G).left (Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation_equal_reduction G t) L
    _ = _ := (eq_div_of_mul_eq' (biextension_dualTranslation_class G L Q e t)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionTranslationLineKernel
