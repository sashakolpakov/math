import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.MapFaithful
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic

/-! # Line Bundle Invariance -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.LineBundleInvariance

noncomputable section

/-! Invariance of an actual line bundle under inversion is preserved by
the geometric pullback, using the actual commuting square. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.Obj

namespace Construction

universe u

def lineBundleInvariantIso_baseChange {X Y : Scheme.{u}} (p : X ⟶ Y)
    (f : X ⟶ X) (g : Y ⟶ Y) (h : f ≫ p = p ≫ g)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (e : (L.pullback g).sheaf ≅ L.sheaf) :
    ((L.pullback p).pullback f).sheaf ≅ (L.pullback p).sheaf :=
  (Scheme.Modules.pullbackComp f p).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr h).app L.sheaf ≪≫
    ((Scheme.Modules.pullbackComp p g).app L.sheaf).symm ≪≫
    (Scheme.Modules.pullback p).mapIso e

variable (K : Type u) [Field K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A]

theorem geometricFiberMap_inv :
    Frobenius.Construction.geometricFiberMap K (GrpObj.inv (X := A)) = (GrpObj.inv (X := Frobenius.Construction.geometricFiberOver K A)).left := by
  unfold Frobenius.Construction.geometricFiberMap
  have h : (Over.pullback (Frobenius.Construction.algebraicClosureBase K)).map (GrpObj.inv (X := A)) =
      GrpObj.inv (X := Frobenius.Construction.geometricFiberOver K A) := by
    rw [GrpObj.inv_eq_inv, Functor.map_inv', CategoryTheory.Functor.map_id, ← GrpObj.inv_eq_inv]
  exact congrArg Over.Hom.left h

theorem geometricLineBundle_symmetric (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hsym : Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf)) :
    Nonempty (((L.pullback (pullback.fst A.hom (Frobenius.Construction.algebraicClosureBase K))).pullback
      (GrpObj.inv (X := Frobenius.Construction.geometricFiberOver K A)).left).sheaf ≅
      (L.pullback (pullback.fst A.hom (Frobenius.Construction.algebraicClosureBase K))).sheaf) := by
  have h := Frobenius.Construction.geometricFiberMap_fst K (GrpObj.inv (X := A))
  rw [geometricFiberMap_inv] at h
  exact ⟨lineBundleInvariantIso_baseChange _ _ _ h L hsym.some⟩

theorem symmetric_lineBundle_tensorPower (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hsym : Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf)) (n : ℕ) :
    Nonempty (((L.tensorPower n).pullback (GrpObj.inv (X := A)).left).sheaf ≅ (L.tensorPower n).sheaf) := by
  have hb : Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (GrpObj.inv (X := A)).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L := Quotient.sound hsym
  have hp : Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (GrpObj.inv (X := A)).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensorPower n)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensorPower n) := by
    simp only [Quotients.FiniteDescent.PicardPowersAdd.Construction.PicardPowers.class_pow, map_pow, hb]
  exact Quotient.exact hp

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.LineBundleInvariance
