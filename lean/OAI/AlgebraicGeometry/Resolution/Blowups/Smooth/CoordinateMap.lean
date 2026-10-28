import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialHypersurface
import Mathlib.Algebra.MvPolynomial.Basic

/-! # Coordinate Map -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoordinateMap.Construction

noncomputable section

/-! A function with derivative one defines a smooth map to the affine line. -/

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
  [Algebra (MvPolynomial Unit k) A] [IsScalarTower k (MvPolynomial Unit k) A]

/-- The same square-zero correction used for a smooth hypersurface also
preserves an arbitrary prescribed value of its coordinate. Thus the whole
ambient algebra is formally smooth over that coordinate line. -/
theorem formallySmooth_over_coordinate [Algebra.FormallySmooth k A]
    (D : Derivation k A A)
    (hD : D (algebraMap (MvPolynomial Unit k) A (MvPolynomial.X ())) = 1) :
    Algebra.FormallySmooth (MvPolynomial Unit k) A := by
  apply Algebra.FormallySmooth.of_comp_surjective
  intro B _ _ I hI g
  let P := MvPolynomial Unit k
  let : Algebra k B := ((algebraMap P B).comp MvPolynomial.C).toAlgebra
  let : IsScalarTower k P B := IsScalarTower.of_algebraMap_eq' rfl
  let z := algebraMap P A (MvPolynomial.X ())
  let t := algebraMap P B (MvPolynomial.X ())
  obtain ⟨f, hf⟩ := Algebra.FormallySmooth.comp_surjective k A I hI (g.restrictScalars k)
  have hzt : Ideal.Quotient.mk I (f z) = Ideal.Quotient.mk I t := by
    calc
      _ = g z := AlgHom.congr_fun hf z
      _ = algebraMap P (B ⧸ I) (MvPolynomial.X ()) := g.commutes (MvPolynomial.X ())
      _ = _ := rfl
  let c := f z - t
  have hc : c ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk I (f z - t) = 0
    rw [map_sub, hzt, sub_self]
  have hsq : c * c = 0 := by
    have h := Ideal.mul_mem_mul hc hc
    rw [← pow_two, hI] at h
    exact h
  let f' := DifferentialHypersurface.Construction.squareZeroDerivationCorrection f D c hsq
  have hf'z : f' z = t := by
    change f z - c * f (D z) = t
    rw [hD, map_one, mul_one]
    exact sub_sub_cancel (f z) t
  have hbase : f'.toRingHom.comp (algebraMap P A) = algebraMap P B := by
    apply MvPolynomial.ringHom_ext
    · intro r
      rw [RingHom.comp_apply]
      change f' (algebraMap P A (algebraMap k P r)) = algebraMap P B (algebraMap k P r)
      rw [← IsScalarTower.algebraMap_apply k P A, ← IsScalarTower.algebraMap_apply k P B]
      exact f'.commutes r
    · intro i
      cases i
      exact hf'z
  let g' : A →ₐ[P] B := { __ := f'.toRingHom, commutes' p := RingHom.congr_fun hbase p }
  refine ⟨g', ?_⟩
  apply AlgHom.ext
  intro a
  change Ideal.Quotient.mk I (f a - c * f (D a)) = g a
  rw [map_sub, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hc, zero_mul, sub_zero]
  exact AlgHom.congr_fun hf a

/-- A unit coordinate derivative gives a smooth affine-line morphism
when the ambient algebra is smooth over its original coefficient ring. -/
theorem smooth_over_coordinate [Algebra.Smooth k A]
    (D : Derivation k A A)
    (hD : D (algebraMap (MvPolynomial Unit k) A (MvPolynomial.X ())) = 1) :
    Algebra.Smooth (MvPolynomial Unit k) A := by
  let : Algebra.FormallySmooth (MvPolynomial Unit k) A := formallySmooth_over_coordinate D hD
  let : Algebra.FinitePresentation (MvPolynomial Unit k) A :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation k (MvPolynomial Unit k) A
  exact ⟨inferInstance, inferInstance⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoordinateMap.Construction
