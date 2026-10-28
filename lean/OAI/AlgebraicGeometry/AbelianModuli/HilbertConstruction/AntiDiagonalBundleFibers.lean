import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.AntiDiagonal

/-! # Anti Diagonal Bundle Fibers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AntiDiagonalBundleFibers

noncomputable section

/-! Pullbacks of the polarization formula's three factors along the anti-diagonal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (L : Line.Bundles.LineBundle A.scheme.left)

def antiDiagonalFirstPullbackIso :
    ((L.pullback (fst A.scheme A.scheme).left).pullback A.antiDiagonalMap.left).sheaf ≅
      (L.pullback ι[A.scheme].left).sheaf :=
  (Scheme.Modules.pullbackComp A.antiDiagonalMap.left (fst A.scheme A.scheme).left).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left A.antiDiagonalMap_fst)).app L.sheaf

def antiDiagonalSecondPullbackIso :
    ((L.pullback (snd A.scheme A.scheme).left).pullback A.antiDiagonalMap.left).sheaf ≅ L.sheaf :=
  (Scheme.Modules.pullbackComp A.antiDiagonalMap.left (snd A.scheme A.scheme).left).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left A.antiDiagonalMap_snd)).app L.sheaf ≪≫
    (Scheme.Modules.pullbackId A.scheme.left).app L.sheaf

def antiDiagonalSumPullbackIso
    (e : (L.pullback η[A.scheme].left).sheaf ≅ Line.Bundles.structureModule S) :
    ((L.pullback μ[A.scheme].left).pullback A.antiDiagonalMap.left).sheaf ≅ Line.Bundles.structureModule A.scheme.left :=
  (Scheme.Modules.pullbackComp A.antiDiagonalMap.left μ[A.scheme].left).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left A.antiDiagonalMap_mul)).app L.sheaf ≪≫
    (Scheme.Modules.pullbackComp A.scheme.hom η[A.scheme].left).symm.app L.sheaf ≪≫
    (Scheme.Modules.pullback A.scheme.hom).mapIso e ≪≫ Line.Bundles.structureModulePullbackIso A.scheme.hom

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AntiDiagonalBundleFibers
