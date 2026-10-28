import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalStalk
import OAI.AlgebraicGeometry.CycleClass.Thom.Local.PolynomialDiagonalRegular

/-! # Diagonal Equations -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalEquations.Constructions

noncomputable section

/-! Polynomial coordinate differences are actual global sections on
the affine geometric product. Their genuine germs form a regular
sequence and generate exactly the native localized diagonal ideal. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace RingTheory.Sequence
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions.CoordinateMaps OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions.StalkCoordinates OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalStalk.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.BalanceIdeal.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Local.PolynomialDiagonalIdeal.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Local.PolynomialDiagonalRegular.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] (n : ℕ)
  [Algebra (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
  [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]

def coordinateDifferenceSection (i : Fin n) : Γ(pullback X.hom X.hom, ⊤) :=
  ProductIs.Constructions.StalkCoordinates.coordinateSection (CommRingCat.of (Γ(X.left, ⊤) ⊗[ℂ] Γ(X.left, ⊤)))
    (pullback X.hom X.hom) (ProductIs.Constructions.affineProductCoordinateIso X X)
    (Tensor.BalanceIdeal.Constructions.difference ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤) (MvPolynomial.X i))

abbrev productLocalRing (x : X.left) : CommRingCat :=
  (pullback X.hom X.hom).presheaf.stalk (pullback.diagonal X.hom x)

def coordinateDifferenceGerms (x : X.left) : List (productLocalRing X x) :=
  List.ofFn (fun i => (pullback X.hom X.hom).presheaf.germ ⊤ (pullback.diagonal X.hom x) trivial
    (coordinateDifferenceSection X n i))

omit [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)] in
theorem coordinateDifferenceGerms_map (x : X.left) :
    (coordinateDifferenceGerms X n x).map (DiagonalStalk.Constructions.diagonalStalkIso X x).hom.hom =
      Local.PolynomialDiagonalIdeal.Constructions.localEquations ℂ Γ(X.left, ⊤) n (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X x) := by
  simp only [coordinateDifferenceGerms, List.map_ofFn, Function.comp_def, Local.PolynomialDiagonalIdeal.Constructions.localEquations]
  apply congrArg List.ofFn
  funext i
  exact DiagonalStalk.Constructions.diagonalStalkIso_section X x (Tensor.BalanceIdeal.Constructions.difference ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤) (MvPolynomial.X i))

omit [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)] in
theorem coordinateDifferenceGerms_length (x : X.left) : (coordinateDifferenceGerms X n x).length = n :=
  List.length_ofFn

variable [Module.Flat (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]

theorem coordinateDifferenceGerms_regular (x : X.left) :
    IsWeaklyRegular (productLocalRing X x) (coordinateDifferenceGerms X n x) := by
  let e := (DiagonalStalk.Constructions.diagonalStalkIso X x).commRingCatIsoToRingEquiv
  have hmap : (coordinateDifferenceGerms X n x).map e =
      Local.PolynomialDiagonalIdeal.Constructions.localEquations ℂ Γ(X.left, ⊤) n (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X x) := coordinateDifferenceGerms_map X n x
  have he : IsWeaklyRegular (productLocalRing X x) (coordinateDifferenceGerms X n x) ↔
      IsWeaklyRegular (Localization.AtPrime (DiagonalStalk.Constructions.diagonalCoordinatePrime X x).asIdeal)
        ((coordinateDifferenceGerms X n x).map e) :=
    e.toAddEquiv.isWeaklyRegular_congr (List.forall₂_map_right_iff.mpr
      (List.forall₂_same.mpr (fun r _ y => e.map_mul r y)))
  apply he.mpr
  rw [hmap]
  exact Local.PolynomialDiagonalRegular.Constructions.localEquations_weaklyRegular ℂ Γ(X.left, ⊤) n (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X x)

omit [Module.Flat (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
  [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)] in
theorem coordinateDifferenceGerms_maximal (x : X.left) :
    ∀ a ∈ coordinateDifferenceGerms X n x, a ∈ IsLocalRing.maximalIdeal (productLocalRing X x) := by
  intro a ha
  let e := (DiagonalStalk.Constructions.diagonalStalkIso X x).commRingCatIsoToRingEquiv
  have hmap : (coordinateDifferenceGerms X n x).map e =
      Local.PolynomialDiagonalIdeal.Constructions.localEquations ℂ Γ(X.left, ⊤) n (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X x) := coordinateDifferenceGerms_map X n x
  have hmem : e a ∈ Local.PolynomialDiagonalIdeal.Constructions.localEquations ℂ Γ(X.left, ⊤) n (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X x) :=
    hmap ▸ List.mem_map.mpr ⟨a, ha, rfl⟩
  have hm := Local.PolynomialDiagonalRegular.Constructions.localEquations_mem_maximal ℂ Γ(X.left, ⊤) n (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X x) (e a) hmem
  let : IsLocalHom e.toRingHom := ⟨fun b hb => by
    exact (congrArg IsUnit (e.symm_apply_apply b)).mp (hb.map e.symm.toMonoidHom)⟩
  exact (congrArg (fun I : Ideal (productLocalRing X x) => a ∈ I)
    (IsLocalRing.maximalIdeal_comap e.toRingHom)).mp hm

variable [Algebra.FormallyUnramified (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
  [IsNoetherianRing (Γ(X.left, ⊤) ⊗[MvPolynomial (Fin n) ℂ] Γ(X.left, ⊤))]

omit [Module.Flat (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)] in
theorem coordinateDifferenceGerms_ideal (x : X.left) :
    (Ideal.ofList (coordinateDifferenceGerms X n x)).map (DiagonalStalk.Constructions.diagonalStalkIso X x).hom.hom =
      (KaehlerDifferential.ideal ℂ Γ(X.left, ⊤)).map
        (algebraMap (Γ(X.left, ⊤) ⊗[ℂ] Γ(X.left, ⊤))
          (Localization.AtPrime (DiagonalStalk.Constructions.diagonalCoordinatePrime X x).asIdeal)) := by
  rw [Ideal.map_ofList, coordinateDifferenceGerms_map]
  exact Local.PolynomialDiagonalIdeal.Constructions.ideal_ofList_localEquations ℂ Γ(X.left, ⊤) n (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X x)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalEquations.Constructions
