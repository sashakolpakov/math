import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoordinateMap
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Adapted Etale Coordinates -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.AdaptedEtaleCoordinates.Construction

noncomputable section

/-! Étale coordinates preserving a specified hypersurface equation. -/

open _root_.MvPolynomial

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] [Algebra.Smooth k A]

/-- A smooth ambient algebra with a unit coordinate derivative has étale
polynomial neighborhoods in which that exact function is a distinguished
coordinate. The other coordinates are obtained relative to its affine line. -/
theorem exists_adapted_etale_coordinates (D : Derivation k A A) (z : A) (hz : D z = 1)
    (q : Ideal A) [q.IsPrime] :
    ∃ f ∉ q, ∃ (n : ℕ) (φ : MvPolynomial (Fin n ⊕ Unit) k →+* Localization.Away f),
      φ.Etale ∧ (∀ r : k, φ (C r) = algebraMap k (Localization.Away f) r) ∧
      φ (X (Sum.inr ())) = algebraMap A (Localization.Away f) z := by
  let P := MvPolynomial Unit k
  let : Algebra P A := (aeval (fun _ : Unit => z)).toRingHom.toAlgebra
  let : IsScalarTower k P A := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    change algebraMap k A r = aeval (fun _ : Unit => z) (C r)
    simp
  have hX : algebraMap P A (X ()) = z := by
    change aeval (fun _ : Unit => z) (X ()) = z
    rw [aeval_X]
  let : Algebra.Smooth P A := Blowups.Smooth.CoordinateMap.Construction.smooth_over_coordinate D (by rw [hX]; exact hz)
  obtain ⟨f, hf, n, a, ht, he⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := P) (S := A) (p := q)
  let B := MvPolynomial (Fin n) P
  let L := Localization.Away f
  let : Algebra B L := a
  let : SMul B L := a.toSMul
  let : IsScalarTower P B L := ht
  let : Algebra.IsStandardEtale B L := he
  let ψ : B →+* L := @algebraMap B L inferInstance inferInstance a
  let e := sumRingEquiv k (Fin n) Unit
  let φ := ψ.comp e.toRingHom
  refine ⟨f, hf, n, φ, ?_, ?_, ?_⟩
  · let U := MvPolynomial (Fin n ⊕ Unit) k
    let : Algebra U B := e.toRingHom.toAlgebra
    let : Algebra U L := φ.toAlgebra
    let : IsScalarTower U B L := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra.Etale U B := RingHom.Etale.of_bijective (f := e.toRingHom) e.bijective
    exact Algebra.Etale.comp U B L
  · intro r
    change ψ (e (C r)) = algebraMap k L r
    rw [sumRingEquiv_C]
    calc
      ψ (C (C r)) = algebraMap P L (C r) :=
        (IsScalarTower.algebraMap_apply P B L (C r)).symm
      _ = algebraMap A L (algebraMap P A (C r)) := IsScalarTower.algebraMap_apply P A L (C r)
      _ = algebraMap A L (algebraMap k A r) := by
        congr 1
        exact (IsScalarTower.algebraMap_apply k P A r).symm
      _ = _ := (IsScalarTower.algebraMap_apply k A L r).symm
  · change ψ (e (X (Sum.inr ()))) = algebraMap A L z
    rw [sumRingEquiv_X_inr]
    calc
      ψ (C (X ())) = algebraMap P L (X ()) :=
        (IsScalarTower.algebraMap_apply P B L (X ())).symm
      _ = algebraMap A L (algebraMap P A (X ())) := IsScalarTower.algebraMap_apply P A L (X ())
      _ = _ := by rw [hX]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.AdaptedEtaleCoordinates.Construction
