import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.FrameCorrection
import Mathlib.Algebra.MvPolynomial.Basic

/-! # Coordinate Frame -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoordinateFrame.Construction

noncomputable section

/-! Smooth morphisms defined by finite families of dual coordinates. -/

variable {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]
  [Fintype ι] [DecidableEq ι]
  [Algebra (MvPolynomial ι k) A] [IsScalarTower k (MvPolynomial ι k) A]

/-- A finite family of coordinate functions with dual relative derivations
defines a formally smooth morphism to its polynomial coordinate base. -/
theorem formallySmooth_over_coordinate_frame [Algebra.FormallySmooth k A]
    (D : ι → Derivation k A A)
    (hD : ∀ i j, D i (algebraMap (MvPolynomial ι k) A (MvPolynomial.X j)) =
      if i = j then 1 else 0) :
    Algebra.FormallySmooth (MvPolynomial ι k) A := by
  apply Algebra.FormallySmooth.of_comp_surjective
  intro B _ _ I hI g
  let P := MvPolynomial ι k
  let : Algebra k B := ((algebraMap P B).comp MvPolynomial.C).toAlgebra
  let : IsScalarTower k P B := IsScalarTower.of_algebraMap_eq' rfl
  let z : ι → A := fun i => algebraMap P A (MvPolynomial.X i)
  let t : ι → B := fun i => algebraMap P B (MvPolynomial.X i)
  obtain ⟨f, hf⟩ := Algebra.FormallySmooth.comp_surjective k A I hI (g.restrictScalars k)
  have hft : ∀ i, Ideal.Quotient.mk I (f (z i)) = Ideal.Quotient.mk I (t i) := by
    intro i
    calc
      _ = g (z i) := AlgHom.congr_fun hf (z i)
      _ = algebraMap P (B ⧸ I) (MvPolynomial.X i) := g.commutes (MvPolynomial.X i)
      _ = _ := rfl
  obtain ⟨f', hmod, hframe⟩ := Coordinate.FrameCorrection.Construction.exists_squareZero_coordinate_correction f D z t hD I hI hft Finset.univ
  have hbase : f'.toRingHom.comp (algebraMap P A) = algebraMap P B := by
    apply MvPolynomial.ringHom_ext
    · intro r
      rw [RingHom.comp_apply]
      change f' (algebraMap P A (algebraMap k P r)) = algebraMap P B (algebraMap k P r)
      rw [← IsScalarTower.algebraMap_apply k P A, ← IsScalarTower.algebraMap_apply k P B]
      exact f'.commutes r
    · intro i
      exact hframe i (Finset.mem_univ i)
  let g' : A →ₐ[P] B := { __ := f'.toRingHom, commutes' p := RingHom.congr_fun hbase p }
  refine ⟨g', ?_⟩
  apply AlgHom.ext
  intro a
  exact (hmod a).trans (AlgHom.congr_fun hf a)

/-- Finite presentation upgrades the coordinate-frame lifting property
to a smooth morphism, allowing the remaining coordinates to be chosen relatively. -/
theorem smooth_over_coordinate_frame [Algebra.Smooth k A]
    (D : ι → Derivation k A A)
    (hD : ∀ i j, D i (algebraMap (MvPolynomial ι k) A (MvPolynomial.X j)) =
      if i = j then 1 else 0) :
    Algebra.Smooth (MvPolynomial ι k) A := by
  let : Algebra.FormallySmooth (MvPolynomial ι k) A := formallySmooth_over_coordinate_frame D hD
  let : Algebra.FinitePresentation (MvPolynomial ι k) A :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation k (MvPolynomial ι k) A
  exact ⟨inferInstance, inferInstance⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoordinateFrame.Construction
