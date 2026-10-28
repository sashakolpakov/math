import OAI.AlgebraicGeometry.FormalGeometry.Completion.FrobeniusLineBundle
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullback

/-! # Frobenius Line Bundle -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.FrobeniusLineBundle.Construction

noncomputable section

/-! The geometric Frobenius tensor-power identity for line bundles defined over the ground field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- A pullback-power isomorphism base-changes along a commuting square. -/
def lineBundlePowerIso_baseChange {X Y : Scheme.{u}} (p : X ⟶ Y)
    (f : X ⟶ X) (g : Y ⟶ Y) (h : f ≫ p = p ≫ g)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (n : ℕ)
    (e : (Scheme.Modules.pullback g).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L.sheaf n) :
    (Scheme.Modules.pullback f).obj (L.pullback p).sheaf ≅
      ((L.pullback p).tensorPower n).sheaf :=
  (Scheme.Modules.pullbackComp f p).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr h).app L.sheaf ≪≫
    ((Scheme.Modules.pullbackComp p g).app L.sheaf).symm ≪≫
    (Scheme.Modules.pullback p).mapIso e ≪≫ Quotients.FiniteDescent.TensorPullback.Construction.TensorPullbackMap.iso p L n

/-- Actual geometric Frobenius pulls a ground-field line bundle back to its q-th power. -/
def geometricFrobeniusLineBundleIso (k : Type u) [Field k] [Fintype k]
    (A : Over (Spec (CommRingCat.of k))) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) :
    (Scheme.Modules.pullback (Frobenius.Construction.geometricSchemeFrobenius k A)).obj
      (L.pullback (pullback.fst A.hom (Frobenius.Construction.algebraicClosureBase k))).sheaf ≅
    ((L.pullback (pullback.fst A.hom (Frobenius.Construction.algebraicClosureBase k))).tensorPower
      (Fintype.card k)).sheaf :=
  lineBundlePowerIso_baseChange (pullback.fst A.hom (Frobenius.Construction.algebraicClosureBase k))
    (Frobenius.Construction.geometricSchemeFrobenius k A) (Frobenius.Construction.finiteFieldSchemeFrobenius k A).left
    (Frobenius.Construction.geometricFiberMap_fst k (Frobenius.Construction.finiteFieldSchemeFrobenius k A)) L (Fintype.card k)
    (FrobeniusLineBundle.Construction.lineBundleFrobeniusIso k (Frobenius.Construction.varietyBaseMap k A) L)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.FrobeniusLineBundle.Construction
