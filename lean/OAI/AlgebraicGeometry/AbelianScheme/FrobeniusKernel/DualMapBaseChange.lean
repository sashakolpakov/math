import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardMapBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizationComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange

/-! # Dual Map Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualMapBaseChange.Construction

noncomputable section

/-! The actual canonical dual map and polarization pullback commute
with arbitrary base change, including nonreduced bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange

namespace NativePicardPullback

variable {S S' : Scheme.{u}} {g h : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
variable (f : S' ⟶ S) (p : A.scheme ⟶ B.scheme) [IsMonHom p]

theorem pullbackHomogeneousSheaf_baseChange_apply (T : Over S')
    (z : (B.pullback f).homogeneousPicardSheaf.obj.obj (op T)) :
    A.homogeneousPicardBaseChangeEquiv f T
        ((PicardPullback.Construction.IntrinsicPicardPullback.pullbackHomogeneousSheaf (PicardMapBaseChange.Construction.IntrinsicPicardPullback.nativeBaseChangeMap f p)).hom.app (op T) z) =
      (PicardPullback.Construction.IntrinsicPicardPullback.pullbackHomogeneousSheaf p).hom.app (op ((Over.map f).obj T))
        (B.homogeneousPicardBaseChangeEquiv f T z) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun r => r.hom) (PicardMapBaseChange.Construction.IntrinsicPicardPullback.pullbackHomogeneousSheaf_baseChange f p)) (op T)) z

theorem dualMap_baseChange (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) :
    (Over.pullback f).map (PicardPullback.Construction.IntrinsicPicardPullback.dualMap p DA DB) =
      PicardPullback.Construction.IntrinsicPicardPullback.dualMap (PicardMapBaseChange.Construction.IntrinsicPicardPullback.nativeBaseChangeMap f p) (DA.pullback f) (DB.pullback f) := by
  apply PicardPullback.Construction.IntrinsicPicardPullback.dualMap_unique (PicardMapBaseChange.Construction.IntrinsicPicardPullback.nativeBaseChangeMap f p) (DA.pullback f) (DB.pullback f)
  intro T x
  apply (A.homogeneousPicardBaseChangeEquiv f T).injective
  exact (DA.pullbackRepresentable_comparison f T _).trans
    ((congrArg DA.representable.homEquiv
      (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map (PicardPullback.Construction.IntrinsicPicardPullback.dualMap p DA DB) f T x)).trans
      ((PicardPullback.Construction.IntrinsicPicardPullback.dualMap_action p DA DB (DB.abelian.baseChangePointsEquiv f T x)).trans
        ((congrArg ((PicardPullback.Construction.IntrinsicPicardPullback.pullbackHomogeneousSheaf p).hom.app (op ((Over.map f).obj T)))
          (DB.pullbackRepresentable_comparison f T x).symm).trans
            (pullbackHomogeneousSheaf_baseChange_apply f p T _).symm)))

end NativePicardPullback

variable {S S' : Scheme.{u}} {g h : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
variable (f : S' ⟶ S) (p : A.scheme ⟶ B.scheme) [IsMonHom p]
variable (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
variable {δ : Fin h → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB δ)

theorem polarizationPullbackHom_baseChange :
    (Over.pullback f).map (PolarizationComparison.Construction.polarizationPullbackHom p DA DB pol) =
      PolarizationComparison.Construction.polarizationPullbackHom (PicardMapBaseChange.Construction.IntrinsicPicardPullback.nativeBaseChangeMap f p)
        (DA.pullback f) (DB.pullback f) (pol.pullback f) := by
  unfold PolarizationComparison.Construction.polarizationPullbackHom
  rw [Functor.map_comp, Functor.map_comp, NativePicardPullback.dualMap_baseChange]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualMapBaseChange.Construction
