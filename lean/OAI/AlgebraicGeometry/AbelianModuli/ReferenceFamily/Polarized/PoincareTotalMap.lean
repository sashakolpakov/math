import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TotalGroupMaps

/-! # Poincare Total Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.PoincareTotalMap

noncomputable section

/-! The actual mixed total-space map of a polarized comparison
preserves the original Poincare line-bundle class across changing bases. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {S T : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N T)
    (f : T ⟶ S) (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso B (A.pullback f))

def polarizedPoincareTotalMap : (B.dual.abelian.scheme ⊗ B.abelian.scheme).left ⟶
    (A.dual.abelian.scheme ⊗ A.abelian.scheme).left :=
  (e.dual.hom ⊗ₘ e.abelian.hom).left ≫ (A.dual.poincarePullbackOverMap f).left

theorem polarizedPoincareTotalMap_class :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (polarizedPoincareTotalMap A B f e)
      (HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare) = HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare := by
  let U := (A.dual.abelian.pullback f).scheme ⊗ (A.abelian.pullback f).scheme
  let m : (B.dual.abelian.scheme ⊗ B.abelian.scheme).left ⟶ U.left :=
    (e.dual.hom ⊗ₘ e.abelian.hom).left
  let p : U.left ⟶ (A.dual.abelian.scheme ⊗ A.abelian.scheme).left :=
    (A.dual.poincarePullbackOverMap f).left
  exact (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp m p (HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare)).trans e.poincare

theorem polarizedPoincareTotalMap_fst :
    polarizedPoincareTotalMap A B f e ≫ (fst A.dual.abelian.scheme A.abelian.scheme).left =
      (fst B.dual.abelian.scheme B.abelian.scheme).left ≫ Dual.TotalGroupMaps.dualTotalMap A B f e := by
  let U := (A.dual.abelian.pullback f).scheme ⊗ (A.abelian.pullback f).scheme
  let m : (B.dual.abelian.scheme ⊗ B.abelian.scheme).left ⟶ U.left :=
    (e.dual.hom ⊗ₘ e.abelian.hom).left
  let p : U.left ⟶ (A.dual.abelian.scheme ⊗ A.abelian.scheme).left :=
    (A.dual.poincarePullbackOverMap f).left
  have hp : p ≫ (fst A.dual.abelian.scheme A.abelian.scheme).left =
      (fst (A.dual.abelian.pullback f).scheme (A.abelian.pullback f).scheme).left ≫
        pullback.fst A.dual.abelian.scheme.hom f :=
    congrArg Over.Hom.left (A.dual.poincarePullbackOverMap_fst f)
  have hm : m ≫ (fst (A.dual.abelian.pullback f).scheme (A.abelian.pullback f).scheme).left =
      (fst B.dual.abelian.scheme B.abelian.scheme).left ≫ e.dual.hom.left :=
    Over.tensorHom_left_fst _ _ _ _
  exact (Category.assoc m p (fst A.dual.abelian.scheme A.abelian.scheme).left).trans
    ((congrArg (fun q => m ≫ q) hp).trans
      ((Category.assoc m (fst (A.dual.abelian.pullback f).scheme (A.abelian.pullback f).scheme).left
        (pullback.fst A.dual.abelian.scheme.hom f)).symm.trans
        ((congrArg (fun q => q ≫ pullback.fst A.dual.abelian.scheme.hom f) hm).trans
          (Category.assoc (fst B.dual.abelian.scheme B.abelian.scheme).left e.dual.hom.left
            (pullback.fst A.dual.abelian.scheme.hom f)))))

theorem polarizedPoincareTotalMap_snd :
    polarizedPoincareTotalMap A B f e ≫ (snd A.dual.abelian.scheme A.abelian.scheme).left =
      (snd B.dual.abelian.scheme B.abelian.scheme).left ≫ TotalMaps.polarizedTotalMap A B f e := by
  let U := (A.dual.abelian.pullback f).scheme ⊗ (A.abelian.pullback f).scheme
  let m : (B.dual.abelian.scheme ⊗ B.abelian.scheme).left ⟶ U.left :=
    (e.dual.hom ⊗ₘ e.abelian.hom).left
  let p : U.left ⟶ (A.dual.abelian.scheme ⊗ A.abelian.scheme).left :=
    (A.dual.poincarePullbackOverMap f).left
  have hp : p ≫ (snd A.dual.abelian.scheme A.abelian.scheme).left =
      (snd (A.dual.abelian.pullback f).scheme (A.abelian.pullback f).scheme).left ≫
        pullback.fst A.abelian.scheme.hom f :=
    congrArg Over.Hom.left (A.dual.poincarePullbackOverMap_snd f)
  have hm : m ≫ (snd (A.dual.abelian.pullback f).scheme (A.abelian.pullback f).scheme).left =
      (snd B.dual.abelian.scheme B.abelian.scheme).left ≫ e.abelian.hom.left :=
    Over.tensorHom_left_snd _ _ _ _
  exact (Category.assoc m p (snd A.dual.abelian.scheme A.abelian.scheme).left).trans
    ((congrArg (fun q => m ≫ q) hp).trans
      ((Category.assoc m (snd (A.dual.abelian.pullback f).scheme (A.abelian.pullback f).scheme).left
        (pullback.fst A.abelian.scheme.hom f)).symm.trans
        ((congrArg (fun q => q ≫ pullback.fst A.abelian.scheme.hom f) hm).trans
          (Category.assoc (snd B.dual.abelian.scheme B.abelian.scheme).left e.abelian.hom.left
            (pullback.fst A.abelian.scheme.hom f)))))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.PoincareTotalMap
