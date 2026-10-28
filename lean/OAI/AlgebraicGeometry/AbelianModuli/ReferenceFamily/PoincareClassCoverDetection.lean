import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FunctionNormalizedPicardDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.BaseChange

/-! # Poincare Class Cover Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareClassCoverDetection

noncomputable section

section

/-! The simultaneous Poincare base change factors through an actual
cover of the dual parameter, by a native product isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {S Y : Scheme.{0}} {g : ℕ} {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : HilbertConstruction.Dual.Data.DualAbelianData A) (u : Y ⟶ S)

def poincareParameterCover : (Over.map u).obj (D.abelian.pullback u).scheme ⟶ D.abelian.scheme :=
  Over.homMk (pullback.fst D.abelian.scheme.hom u) pullback.condition

instance poincareParameterCover_flat [Flat u] : Flat (poincareParameterCover D u).left :=
  inferInstanceAs (Flat (pullback.fst D.abelian.scheme.hom u))

instance poincareParameterCover_surjective [Surjective u] : Surjective (poincareParameterCover D u).left :=
  inferInstanceAs (Surjective (pullback.fst D.abelian.scheme.hom u))

instance poincareParameterCover_quasiCompact [QuasiCompact u] : QuasiCompact (poincareParameterCover D u).left :=
  inferInstanceAs (QuasiCompact (pullback.fst D.abelian.scheme.hom u))

theorem poincareParameterCover_factor :
    (HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A.scheme u (D.abelian.pullback u).scheme).hom ≫
      (poincareParameterCover D u ▷ A.scheme).left = (D.poincarePullbackOverMap u).left := by
  let V := (Over.map u).obj (D.abelian.pullback u).scheme
  let c := (HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A.scheme u (D.abelian.pullback u).scheme).hom
  let q := poincareParameterCover D u
  have hf : (q ▷ A.scheme).left ≫ (fst D.abelian.scheme A.scheme).left =
      (fst V A.scheme).left ≫ q.left := congrArg Over.Hom.left (whiskerRight_fst q A.scheme)
  have hs : (q ▷ A.scheme).left ≫ (snd D.abelian.scheme A.scheme).left =
      (snd V A.scheme).left := congrArg Over.Hom.left (whiskerRight_snd q A.scheme)
  have hcf : c ≫ (fst V A.scheme).left = (fst (D.abelian.pullback u).scheme (A.pullback u).scheme).left :=
    HilbertConstruction.Picard.BaseChange.familyBaseChangeIso_hom_fst A.scheme u (D.abelian.pullback u).scheme
  have hcs : c ≫ (snd V A.scheme).left =
      (snd (D.abelian.pullback u).scheme (A.pullback u).scheme).left ≫ pullback.fst A.scheme.hom u :=
    HilbertConstruction.Picard.BaseChange.familyBaseChangeIso_hom_snd A.scheme u (D.abelian.pullback u).scheme
  apply Over.tensorObj_ext
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun z => c ≫ z) hf).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ q.left) hcf).trans
            (D.poincarePullbackOverMap_left_fst u).symm)))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun z => c ≫ z) hs).trans
        (hcs.trans (D.poincarePullbackOverMap_left_snd u).symm))

end

/-! Native normalized line classes on the Poincare product are detected
by the actual simultaneous base change of the abelian and dual families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

theorem poincareClass_eq_of_baseChange {S Y : Scheme.{0}} {g : ℕ} {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (D : HilbertConstruction.Dual.Data.DualAbelianData A) (u : Y ⟶ S) [Flat u] [Surjective u] [QuasiCompact u]
    (hΓ : ∀ V : Over S, IsIso (fst V A.scheme).left.appTop)
    (L M : HilbertConstruction.Line.Bundles.LineBundle (D.abelian.scheme ⊗ A.scheme).left)
    (eL : (HilbertConstruction.Line.Bundles.LineBundle.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A D.abelian.scheme).left L).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule D.abelian.scheme.left)
    (eM : (HilbertConstruction.Line.Bundles.LineBundle.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A D.abelian.scheme).left M).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule D.abelian.scheme.left)
    (h : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (D.poincarePullbackOverMap u).left (HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (D.poincarePullbackOverMap u).left (HilbertConstruction.Line.Bundles.LineBundle.classOf M)) :
    HilbertConstruction.Line.Bundles.LineBundle.classOf L = HilbertConstruction.Line.Bundles.LineBundle.classOf M := by
  apply FunctionNormalizedPicardDescent.FunctionNormalizedPicard.lineClass_eq_of_parameter_pullback A hΓ (poincareParameterCover D u) L M eL eM
  let c := HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A.scheme u (D.abelian.pullback u).scheme
  let q := (poincareParameterCover D u ▷ A.scheme).left
  apply (HilbertConstruction.Line.Bundles.LineBundle.pullbackIso c).injective
  exact (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp c.hom q (HilbertConstruction.Line.Bundles.LineBundle.classOf L)).symm.trans
    ((congrArg (fun f => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (HilbertConstruction.Line.Bundles.LineBundle.classOf L)) (poincareParameterCover_factor D u)).trans
      (h.trans ((congrArg (fun f => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (HilbertConstruction.Line.Bundles.LineBundle.classOf M))
        (poincareParameterCover_factor D u).symm).trans (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp c.hom q (HilbertConstruction.Line.Bundles.LineBundle.classOf M)))))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareClassCoverDetection
