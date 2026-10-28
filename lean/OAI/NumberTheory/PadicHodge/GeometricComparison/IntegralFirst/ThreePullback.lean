import OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.FunctorialMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeSheafUnit
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.SheafificationPullbackSquare
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.SheafPullbackAdjoint

/-! # Three Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreePullback.IntegralFirstThreePullback

noncomputable section

/-! Actual geometric pullback on the first three integral de Rham terms is
compatible with the native sheafification unit and inverse-image adjunction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits ZeroObject _root_.AlgebraicGeometry

variable {R : Type} [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)

local notation "PX" => OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)
local notation "PY" => OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R Y)
local notation "KX" => OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)
local notation "KY" => OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y)
local notation "UX" => sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat R)
local notation "UY" => sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat R)

def presheafMap : PY ⟶ ((DeRham.Int.directImagePresheaf f).mapHomologicalComplex (.up ℕ)).obj PX :=
  FirstThree.FunctorialMap.FirstThreeFunctorialMap.direct (DeRham.Int.directImagePresheaf f) (DeRham.Int.presheafPullback f)

def sheafMap : ((DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℕ)).obj KY ⟶ KX :=
  FirstThree.FunctorialMap.FirstThreeFunctorialMap.map (DeRham.Int.inverseImage f) (DeRham.Int.sheafPullback f)

def sheafDirect : KY ⟶ ((DeRham.Int.directImage f).mapHomologicalComplex (.up ℕ)).obj KX :=
  FirstThree.FunctorialMap.FirstThreeFunctorialMap.direct (DeRham.Int.directImage f) (DeRham.Int.sheafDirectImage f)

def underlyingMap : ((UY).mapHomologicalComplex (.up ℕ)).obj KY ⟶
    ((DeRham.Int.directImagePresheaf f).mapHomologicalComplex (.up ℕ)).obj
      (((UX).mapHomologicalComplex (.up ℕ)).obj KX) :=
  ((UY).mapHomologicalComplex (.up ℕ)).map (sheafDirect f)

theorem unit_square : ThreeSheafUnit.IntegralFirstThreeSheafUnit.map R Y ≫ underlyingMap f =
    presheafMap f ≫ ((DeRham.Int.directImagePresheaf f).mapHomologicalComplex (.up ℕ)).map
      (ThreeSheafUnit.IntegralFirstThreeSheafUnit.map R X) := by
  apply HomologicalComplex.Hom.ext
  funext n
  rcases n with _ | (_ | (_ | n))
  · change (ThreeSheafUnit.IntegralFirstThreeSheafUnit.map R Y).f 0 ≫ (UY).map ((sheafDirect f).f 0) =
      (presheafMap f).f 0 ≫ (DeRham.Int.directImagePresheaf f).map ((ThreeSheafUnit.IntegralFirstThreeSheafUnit.map R X).f 0)
    rw [show (sheafDirect f).f 0 = (DeRham.Int.sheafDirectImage f).f 0 from FirstThree.FunctorialMap.FirstThreeFunctorialMap.direct_zero _ _,
      show (presheafMap f).f 0 = (DeRham.Int.presheafPullback f).f 0 from FirstThree.FunctorialMap.FirstThreeFunctorialMap.direct_zero _ _]
    exact congrArg (fun a => a.f 0) (DeRham.SheafificationPullbackSquare.presheaf_sheaf_pullback_square f)
  · change (ThreeSheafUnit.IntegralFirstThreeSheafUnit.map R Y).f 1 ≫ (UY).map ((sheafDirect f).f 1) =
      (presheafMap f).f 1 ≫ (DeRham.Int.directImagePresheaf f).map ((ThreeSheafUnit.IntegralFirstThreeSheafUnit.map R X).f 1)
    rw [show (sheafDirect f).f 1 = (DeRham.Int.sheafDirectImage f).f 1 from FirstThree.FunctorialMap.FirstThreeFunctorialMap.direct_one _ _,
      show (presheafMap f).f 1 = (DeRham.Int.presheafPullback f).f 1 from FirstThree.FunctorialMap.FirstThreeFunctorialMap.direct_one _ _]
    exact congrArg (fun a => a.f 1) (DeRham.SheafificationPullbackSquare.presheaf_sheaf_pullback_square f)
  · change (ThreeSheafUnit.IntegralFirstThreeSheafUnit.map R Y).f 2 ≫ (UY).map ((sheafDirect f).f 2) =
      (presheafMap f).f 2 ≫ (DeRham.Int.directImagePresheaf f).map ((ThreeSheafUnit.IntegralFirstThreeSheafUnit.map R X).f 2)
    rw [show (sheafDirect f).f 2 = (DeRham.Int.sheafDirectImage f).f 2 from FirstThree.FunctorialMap.FirstThreeFunctorialMap.direct_two _ _,
      show (presheafMap f).f 2 = (DeRham.Int.presheafPullback f).f 2 from FirstThree.FunctorialMap.FirstThreeFunctorialMap.direct_two _ _]
    exact congrArg (fun a => a.f 2) (DeRham.SheafificationPullbackSquare.presheaf_sheaf_pullback_square f)
  · exact ((DeRham.Int.directImagePresheaf f).map_isZero
      ((UX).map_isZero (isZero_zero (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X)))).eq_of_tgt _ _

theorem sheafMap_adjoint (n : ℕ) :
    (DeRham.Int.imageAdjunction f).homEquiv _ _ ((sheafMap f).f n) = (sheafDirect f).f n := by
  rcases n with _ | (_ | (_ | n))
  · rw [show (sheafMap f).f 0 = (DeRham.Int.sheafPullback f).f 0 from FirstThree.FunctorialMap.FirstThreeFunctorialMap.map_zero _ _,
      show (sheafDirect f).f 0 = (DeRham.Int.sheafDirectImage f).f 0 from FirstThree.FunctorialMap.FirstThreeFunctorialMap.direct_zero _ _]
    exact DeRham.SheafPullbackAdjoint.sheafPullback_adjoint f 0
  · rw [show (sheafMap f).f 1 = (DeRham.Int.sheafPullback f).f 1 from FirstThree.FunctorialMap.FirstThreeFunctorialMap.map_one _ _,
      show (sheafDirect f).f 1 = (DeRham.Int.sheafDirectImage f).f 1 from FirstThree.FunctorialMap.FirstThreeFunctorialMap.direct_one _ _]
    exact DeRham.SheafPullbackAdjoint.sheafPullback_adjoint f 1
  · rw [show (sheafMap f).f 2 = (DeRham.Int.sheafPullback f).f 2 from FirstThree.FunctorialMap.FirstThreeFunctorialMap.map_two _ _,
      show (sheafDirect f).f 2 = (DeRham.Int.sheafDirectImage f).f 2 from FirstThree.FunctorialMap.FirstThreeFunctorialMap.direct_two _ _]
    exact DeRham.SheafPullbackAdjoint.sheafPullback_adjoint f 2
  · exact (isZero_zero (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y)).eq_of_src _ _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreePullback.IntegralFirstThreePullback
