import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoordinateMap
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoordinateFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.SubsetCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.FlatQuotientRegularity
import Mathlib.RingTheory.Smooth.Flat

/-! # Coordinate Regularity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.CoordinateRegularity

noncomputable section

/-! Dual coordinates in a smooth algebra form a regular coordinate system
over an arbitrary commutative base ring. Flatness over the polynomial
coordinate algebra replaces characteristic-zero differentiation arguments. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open _root_.MvPolynomial

theorem coordinate_isRegular {k A : Type*} [CommRing k] [CommRing A]
    [Algebra k A] [Algebra.Smooth k A]
    (D : Derivation k A A) (z : A) (hDz : D z = 1) : IsRegular z := by
  let P := MvPolynomial Unit k
  let φ : P →ₐ[k] A := aeval (fun _ : Unit => z)
  let : Algebra P A := φ.toRingHom.toAlgebra
  let : IsScalarTower k P A :=
    IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  have hz : algebraMap P A (X ()) = z := aeval_X _ _
  let : Algebra.Smooth P A := AlgebraicGeometry.Resolution.Blowups.Smooth.CoordinateMap.Construction.smooth_over_coordinate D (by rw [hz]; exact hDz)
  have h : IsSMulRegular A (X () : P) :=
    Module.Flat.isSMulRegular_of_isRegular MvPolynomial.isRegular_X
  have hl : IsLeftRegular z := by
    change Function.Injective (fun x : A => z * x)
    change Function.Injective (fun x : A => algebraMap P A (X ()) * x) at h
    rw [hz] at h
    exact h
  exact ⟨hl, fun x y hxy => hl (by simpa only [mul_comm] using hxy)⟩

universe u

theorem polynomial_coordinate_regular_mod_subset {k ι : Type u} [CommRing k] [DecidableEq ι]
    (s : Finset ι) (j : ι) (hj : j ∉ s) :
    IsRegular (Ideal.Quotient.mk (AlgebraicGeometry.Resolution.Blowups.SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := k) s) (X j)) := by
  let e := AlgebraicGeometry.Resolution.Blowups.Smooth.SubsetCenter.Construction.subsetCoordinateCenterAlgEquiv (R := k) s
  have he : e (Ideal.Quotient.mk (AlgebraicGeometry.Resolution.Blowups.SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := k) s) (X j)) =
      (X ⟨j, hj⟩ : MvPolynomial {i : ι // i ∉ s} k) :=
    AlgebraicGeometry.Resolution.Blowups.Smooth.SubsetCenter.Construction.deleteCenterCoordinates_X_out s j hj
  have hl : IsLeftRegular (Ideal.Quotient.mk (AlgebraicGeometry.Resolution.Blowups.SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := k) s) (X j)) := by
    intro x y hxy
    apply e.injective
    apply (MvPolynomial.isRegular_X (R := k) (n := (⟨j, hj⟩ : {i : ι // i ∉ s}))).left
    have h := congrArg e hxy
    simpa only [map_mul, he] using h
  exact ⟨hl, fun x y hxy => hl (by simpa only [mul_comm] using hxy)⟩

theorem family_coordinate_regular_mod_subset {k A ι : Type u}
    [CommRing k] [CommRing A] [Algebra k A] [Algebra.Smooth k A]
    [Fintype ι] [DecidableEq ι]
    (z : ι → A) (D : ι → Derivation k A A)
    (hD : ∀ i j, D i (z j) = if i = j then 1 else 0)
    (s : Finset ι) (j : ι) (hj : j ∉ s) :
    IsRegular (Ideal.Quotient.mk (Ideal.span (z '' (s : Set ι))) (z j)) := by
  let P := MvPolynomial ι k
  let φ : P →ₐ[k] A := aeval z
  let : Algebra P A := φ.toRingHom.toAlgebra
  let : IsScalarTower k P A :=
    IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  have hz (i : ι) : algebraMap P A (X i) = z i := aeval_X z i
  let : Algebra.Smooth P A := AlgebraicGeometry.Resolution.Blowups.Smooth.CoordinateFrame.Construction.smooth_over_coordinate_frame D (by
    intro i j
    rw [hz]
    exact hD i j)
  have hideal : (AlgebraicGeometry.Resolution.Blowups.SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := k) s).map (algebraMap P A) =
      Ideal.span (z '' (s : Set ι)) := by
    rw [AlgebraicGeometry.Resolution.Blowups.SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal, Ideal.map_span, Set.image_image]
    congr 1
    congr 1
    funext i
    exact hz i
  have h := AlgebraicGeometry.Resolution.Blowups.FlatQuotientRegularity.Construction.flat_extended_quotient_regular (S := A)
    (AlgebraicGeometry.Resolution.Blowups.SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := k) s) (X j) (polynomial_coordinate_regular_mod_subset s j hj)
  rw [hideal, hz] at h
  exact h

theorem family_coordinate_regular_mod_preceding {k A : Type u}
    [CommRing k] [CommRing A] [Algebra k A] [Algebra.Smooth k A] {r : ℕ}
    (z : Fin r → A) (D : Fin r → Derivation k A A)
    (hD : ∀ i j, D i (z j) = if i = j then 1 else 0) (j : Fin r) :
    IsRegular (Ideal.Quotient.mk
      (Ideal.span (z '' {i : Fin r | i < j})) (z j)) := by
  let v : ULift.{u} (Fin r) → A := fun i => z i.down
  let E : ULift.{u} (Fin r) → Derivation k A A := fun i => D i.down
  let s := Finset.univ.filter (fun i : ULift.{u} (Fin r) => i.down < j)
  have hE (i l : ULift.{u} (Fin r)) : E i (v l) = if i = l then 1 else 0 := by
    simpa only [E, v, ← ULift.ext_iff] using hD i.down l.down
  have hs : (ULift.up j : ULift.{u} (Fin r)) ∉ s := by simp [s]
  have himage : v '' (s : Set (ULift.{u} (Fin r))) = z '' {i : Fin r | i < j} := by
    ext a
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i.down, (Finset.mem_filter.mp hi).2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨ULift.up i, by simpa [s] using hi, rfl⟩
  have h := family_coordinate_regular_mod_subset v E hE s (ULift.up j) hs
  rw [himage] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.CoordinateRegularity
