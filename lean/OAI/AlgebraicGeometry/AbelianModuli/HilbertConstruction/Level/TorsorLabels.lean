import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.SplitSelfPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.TranslationLabels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.ProductLabels

/-! # Torsor Labels -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The second projection on each labeled component of the full-level self-pullback is exactly the torsion translation used in the action on regular functions. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {S : Scheme.{u}} {g N : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (level : A.FullLevel N)

theorem Abelian.Schemes.AbelianScheme.fullLevelKernelTorsorIso_label_snd
    (i : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    Constant.ProductLabels.constantProductLabel A.scheme _ i ≫ (A.fullLevelKernelTorsorIso level).hom ≫
      Limits.pullback.snd (A.multiplication N) (A.multiplication N) =
        A.basePointTranslation (A.fullLevelBaseTorsionPoints level i).val := by
  let q : A.scheme ⟶ A.scheme ⊗ Level.Scheme.constantFullLevelScheme g N S := Constant.ProductLabels.constantProductLabel A.scheme _ i
  have hf : q ≫ fst A.scheme (Level.Scheme.constantFullLevelScheme g N S) = 𝟙 A.scheme := lift_fst _ _
  have hs : q ≫ (snd A.scheme (Level.Scheme.constantFullLevelScheme g N S) ≫
      level.schemeIso.hom ≫ A.torsionInclusion N) =
        toUnit A.scheme ≫ (A.fullLevelBaseTorsionPoints level i).val :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ level.schemeIso.hom ≫ A.torsionInclusion N)
        (lift_snd (𝟙 A.scheme) (toUnit A.scheme ≫ ConstantScheme.Morphisms.constantSchemeLabelPoint S _ i))).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun k => toUnit A.scheme ≫ k) (A.fullLevelSchemeIso_label level i))))
  exact (congrArg (fun k => q ≫ k) (A.fullLevelKernelTorsorIso_snd level)).trans
    ((MonObj.comp_mul _ _ _).trans
      ((congrArg₂ (fun a b : A.scheme ⟶ A.scheme => a * b) hf hs).trans (mul_comm _ _)))

theorem Abelian.Schemes.AbelianScheme.fullLevelSplitSelfPullbackIso_label_snd
    (i : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    Limits.Sigma.ι (fun _ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) => A.scheme.left) i ≫
      (A.fullLevelSplitSelfPullbackIso level).hom ≫
        Limits.pullback.snd (A.multiplication N).left (A.multiplication N).left =
          (A.basePointTranslation (A.fullLevelBaseTorsionPoints level i).val).left := by
  let c : A.scheme.left ⟶ (Level.Scheme.constantFullLevelScheme g N A.scheme.left).left :=
    Limits.Sigma.ι (fun _ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) => A.scheme.left) i
  let t := (ConstantScheme.Product.constantSchemeProductIso A.scheme (ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)))).hom
  let e := (A.fullLevelKernelTorsorIso level).hom.left
  let d := (HilbertConstruction.Over.DiagonalComparison.overSelfPullbackIso (A.multiplication N)).hom
  have hs : d ≫ Limits.pullback.snd (A.multiplication N).left (A.multiplication N).left =
      (Limits.pullback.snd (A.multiplication N) (A.multiplication N)).left :=
    ((IsPullback.of_hasPullback (A.multiplication N) (A.multiplication N)).map
      (Over.forget S)).isoPullback_hom_snd
  have he : (A.fullLevelSplitSelfPullbackIso level).hom ≫
      Limits.pullback.snd (A.multiplication N).left (A.multiplication N).left =
        t ≫ e ≫ (Limits.pullback.snd (A.multiplication N) (A.multiplication N)).left :=
    (Category.assoc _ _ _).trans (congrArg (fun k => t ≫ k)
      ((Category.assoc _ _ _).trans (congrArg (fun k => e ≫ k) hs)))
  exact (congrArg (fun k => c ≫ k) he).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun k : A.scheme.left ⟶ (A.scheme ⊗ Level.Scheme.constantFullLevelScheme g N S).left =>
        k ≫ e ≫ (Limits.pullback.snd (A.multiplication N) (A.multiplication N)).left)
        (Constant.ProductLabels.constantSchemeProductIso_label A.scheme _ i)).trans
          (congrArg (fun k : A.scheme ⟶ A.scheme => k.left)
            (A.fullLevelKernelTorsorIso_label_snd level i))))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
