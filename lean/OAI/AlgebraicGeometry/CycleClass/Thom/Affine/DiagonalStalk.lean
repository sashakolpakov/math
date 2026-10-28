import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.LocalDiagonalEuler

/-! # Diagonal Stalk -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalStalk.Constructions

noncomputable section

/-! At an actual affine diagonal point, the geometric product stalk
is the localization at the native tensor-product diagonal prime.
The comparison sends each coordinate section to its actual localization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions.CoordinateMaps OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions.StalkCoordinates
open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.LocalDiagonalEuler

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def stalkCoordinateIsoAt (R : CommRingCat) (Y : Scheme) (e : Y ≅ Spec R) (y : Y)
    (q : PrimeSpectrum R) (hq : e.hom y = q) :
    Y.presheaf.stalk y ≅ CommRingCat.of (Localization.AtPrime q.asIdeal) :=
  ProductIs.Constructions.StalkCoordinates.stalkCoordinateIso R Y e y ≪≫
    eqToIso (congrArg (fun p : PrimeSpectrum R => CommRingCat.of (Localization.AtPrime p.asIdeal)) hq)

theorem coordinateSection_germ_at (R : CommRingCat) (Y : Scheme) (e : Y ≅ Spec R) (y : Y)
    (q : PrimeSpectrum R) (hq : e.hom y = q) (r : R) :
    (stalkCoordinateIsoAt R Y e y q hq).hom (Y.presheaf.germ ⊤ y trivial (ProductIs.Constructions.StalkCoordinates.coordinateSection R Y e r)) =
      algebraMap R (Localization.AtPrime q.asIdeal) r := by
  cases hq
  exact ProductIs.Constructions.StalkCoordinates.coordinateSection_germ R Y e y r

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]

def diagonalCoordinatePrime (x : X.left) : PrimeSpectrum (Γ(X.left, ⊤) ⊗[ℂ] Γ(X.left, ⊤)) :=
  TorAlgebra.LocalDiagonalEuler.diagonalPrime ℂ Γ(X.left, ⊤) (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X x)

theorem coordinate_diagonal_point (x : X.left) :
    (ProductIs.Constructions.affineProductCoordinateIso X X).hom (pullback.diagonal X.hom x) = diagonalCoordinatePrime X x :=
  congrArg (fun f : X.left ⟶ Spec (CommRingCat.of (Γ(X.left, ⊤) ⊗[ℂ] Γ(X.left, ⊤))) => f x)
    (ProductIs.Constructions.CoordinateMaps.coordinateIso_diagonal X)

def diagonalStalkIso (x : X.left) :
    (pullback X.hom X.hom).presheaf.stalk (pullback.diagonal X.hom x) ≅
      CommRingCat.of (Localization.AtPrime (diagonalCoordinatePrime X x).asIdeal) :=
  stalkCoordinateIsoAt (CommRingCat.of (Γ(X.left, ⊤) ⊗[ℂ] Γ(X.left, ⊤)))
    (pullback X.hom X.hom) (ProductIs.Constructions.affineProductCoordinateIso X X) (pullback.diagonal X.hom x)
    (diagonalCoordinatePrime X x) (coordinate_diagonal_point X x)

theorem diagonalStalkIso_section (x : X.left) (r : Γ(X.left, ⊤) ⊗[ℂ] Γ(X.left, ⊤)) :
    (diagonalStalkIso X x).hom
      ((pullback X.hom X.hom).presheaf.germ ⊤ (pullback.diagonal X.hom x) trivial
        (ProductIs.Constructions.StalkCoordinates.coordinateSection (CommRingCat.of (Γ(X.left, ⊤) ⊗[ℂ] Γ(X.left, ⊤)))
          (pullback X.hom X.hom) (ProductIs.Constructions.affineProductCoordinateIso X X) r)) =
      algebraMap (Γ(X.left, ⊤) ⊗[ℂ] Γ(X.left, ⊤)) (Localization.AtPrime (diagonalCoordinatePrime X x).asIdeal) r :=
  coordinateSection_germ_at (CommRingCat.of (Γ(X.left, ⊤) ⊗[ℂ] Γ(X.left, ⊤)))
    (pullback X.hom X.hom) (ProductIs.Constructions.affineProductCoordinateIso X X) (pullback.diagonal X.hom x)
    (diagonalCoordinatePrime X x) (coordinate_diagonal_point X x) r

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalStalk.Constructions
