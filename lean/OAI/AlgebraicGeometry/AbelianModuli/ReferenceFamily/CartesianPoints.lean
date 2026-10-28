import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianFiberComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.BaseChange

/-! # Cartesian Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianPoints.CartesianFamily

noncomputable section

section

/-! A native cartesian family comparison identifies every test point
with its actual image in the descended family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S Y : Scheme.{0}} (u : Y ⟶ S) (A : Over Y) (B : Over S)
    (e : A ≅ (Over.pullback u).obj B)

def pointsEquiv (T : Over Y) : (T ⟶ A) ≃ ((Over.map u).obj T ⟶ B) :=
  e.homToEquiv.trans ((Over.mapPullbackAdj u).homEquiv T B).symm

theorem pointsEquiv_factor (q : (Over.map u).obj A ⟶ B)
    (hq : q.left = CartesianFiberComparison.CartesianFamily.totalMap u A B e) (T : Over Y) (a : T ⟶ A) :
    pointsEquiv u A B e T a = (Over.map u).map a ≫ q := by
  apply Over.OverMorphism.ext
  change (a.left ≫ e.hom.left) ≫ pullback.fst B.hom u = a.left ≫ q.left
  exact (Category.assoc _ _ _).trans (congrArg (fun f => a.left ≫ f) hq.symm)

end

/-! The native cartesian identification of abelian points preserves
the actual identity section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem abelian_pointsEquiv_one {S Y : Scheme.{0}} {g : ℕ} (u : Y ⟶ S)
    (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Y) (B : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (e : A.scheme ≅ (B.pullback u).scheme) [IsMonHom e.hom] (T : Over Y) :
    pointsEquiv u A.scheme B.scheme e T (1 : T ⟶ A.scheme) = 1 := by
  change B.baseChangePointsEquiv u T ((1 : T ⟶ A.scheme) ≫ e.hom) = 1
  exact (congrArg (B.baseChangePointsEquiv u T) (MonObj.one_comp e.hom)).trans
    (B.baseChangePointsMulEquiv u T).map_one

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianPoints.CartesianFamily
