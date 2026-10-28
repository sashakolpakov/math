import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.SupportedCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.OrderedCechEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexHorizontalEdge

/-! # Supported Recovery -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.SupportedRecovery

noncomputable section

/-! The original supported lift, followed by relative Čech extension,
is the original global Čech edge on the whole complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Intersections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (D : Type (u+1)) [Category.{u} D] [Abelian D] [HasLimitsOfSize.{u,u} D]
  [HasCoproducts.{0} D]
  (X : TopCat.{u}) (U : Opens X) {ι : Type u} [LinearOrder ι] (V : ι → Opens X)
  (O : Opens X) (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) D) ℕ)
  (hzero : ∀ q, IsZero ((K.X q).obj.obj (op O)))
  (hV : ∀ i, V i ≤ O)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Intersections.intersect U
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.SupportedCoordinates.terminalOpen X U
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.SupportedCoordinates.underlying D X K

def localLift : Presheaf.OrderedCechEdge.sections P ⟶
    (Total.source U V P).total (.up ℕ) :=
  Supported.ZeroComplementComplex.lift O A K hzero ≫
    SupportedOrderedCechEdge.Abelian.map D X F V O K
      (fun i => inf_le_right.trans (hV i))

theorem recovery :
    localLift D X U V O K hzero hV ≫ Total.map U V P =
      Presheaf.OrderedCechEdge.edge (Intersections.cover U V) P :=
  BicomplexHorizontalEdge.Precompose.recovery
    (SupportedOrderedCechEdge.Abelian.bicomplex D X F V K)
    (SupportedOrderedCechEdge.Abelian.source D X F O K)
    (SupportedOrderedCechEdge.Abelian.component D X F V O K)
    (fun q q' _ => SupportedOrderedCechEdge.Abelian.comm D X F V O K q q')
    (SupportedOrderedCechEdge.Abelian.cocycle D X F V O K
      (fun i => inf_le_right.trans (hV i)))
    (Presheaf.OrderedCechEdge.bicomplex (Intersections.cover U V) P)
    (Presheaf.OrderedCechEdge.sections P)
    (fun q => Presheaf.OrderedCechEdge.augmentation (Intersections.cover U V) ((P).X q))
    (fun q q' _ => Presheaf.OrderedCechEdge.augmentation_comm (Intersections.cover U V) P q q')
    (Presheaf.OrderedCechEdge.augmentation_cocycle (Intersections.cover U V) P)
    (Total.bicomplexMap U V P)
    (Supported.ZeroComplementComplex.lift O A K hzero)
    (SupportedCoordinates.global_component D X U V O K hzero hV)

theorem homology_recovery (n : ℕ) :
    HomologicalComplex.homologyMap (localLift D X U V O K hzero hV) n ≫
        HomologicalComplex.homologyMap (Total.map U V P) n =
      HomologicalComplex.homologyMap (Presheaf.OrderedCechEdge.edge (Intersections.cover U V) P) n := by
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun f => HomologicalComplex.homologyMap f n) (recovery D X U V O K hzero hV)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.SupportedRecovery
