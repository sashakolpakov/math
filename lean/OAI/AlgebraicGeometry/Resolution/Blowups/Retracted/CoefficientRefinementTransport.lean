import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.CoefficientRefinement
import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.DerivationNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.CoefficientStep
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoefficientNaturality

/-! # Coefficient Refinement Transport -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.CoefficientRefinementTransport.Construction

noncomputable section

/-! Exact retained ideals and normal derivatives when the coefficient ring is refined. -/

open _root_.Polynomial

section Ideals

variable {H B R V : Type*} [CommRing H] [CommRing B] [CommRing R] [CommRing V]

/-- A commuting retraction square identifies the refined retained ideal
with the actual extension of the old coefficient ideal. -/
theorem retracted_coefficient_refinement_map
    (f : R →+* V) (φ : H →+* B) (z : R)
    (e : (R ⧸ Ideal.span {z}) ≃+* H) (e' : (V ⧸ Ideal.span {f z}) ≃+* B)
    (h : e'.toRingHom.comp ((Ideal.Quotient.mk (Ideal.span {f z})).comp f) =
      φ.comp (e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {z}))))
    (C : Ideal (R ⧸ Ideal.span {z})) :
    (C.map (Relative.CoefficientBaseChange.Construction.mappedHypersurfaceQuotientMap f z)).map e'.toRingHom =
      (C.map e.toRingHom).map φ := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact RingHom.congr_fun h r

end Ideals

section Normal

variable {H B R V : Type*} [CommRing H] [CommRing B] [CommRing R] [CommRing V]
  [Algebra H B] [Algebra H R] [Algebra H V] [Algebra B V] [IsScalarTower H B V]
  [Algebra H[X] R] [IsScalarTower H H[X] R] [Algebra.Etale H[X] R]
  [Algebra B[X] V] [IsScalarTower B B[X] V] [Algebra.Etale B[X] V]

/-- The newly constructed normal derivative agrees on the old ambient
ring when an actual refinement respects the line coordinate and coefficients. -/
theorem etaleLine_normalDerivation_coefficient_refinement
    (f : R →ₐ[H] V) (hcoord : f (algebraMap H[X] R X) = algebraMap B[X] V X) (x : R) :
    HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation (H := B) (V := V) (f x) =
      f (HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation (H := H) (V := R) x) := by
  let : Algebra R V := f.toRingHom.toAlgebra
  let : IsScalarTower H R V := IsScalarTower.of_algebraMap_eq (fun h => (f.commutes h).symm)
  let : Algebra H[X] V := (f.toRingHom.comp (algebraMap H[X] R)).toAlgebra
  let : IsScalarTower H[X] R V := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower H H[X] V := IsScalarTower.of_algebraMap_eq (by
    intro h
    change algebraMap H V h = f (algebraMap H[X] R (algebraMap H H[X] h))
    rw [← IsScalarTower.algebraMap_apply H H[X] R, f.commutes])
  let E : Derivation H V V :=
    (HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation (H := B) (V := V)).restrictScalars H
  apply EtaleLine.DerivationNaturality.Construction.etaleLine_normalDerivation_natural E
  change HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation (H := B) (V := V)
    (f (algebraMap H[X] R X)) = 1
  rw [hcoord]
  exact HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation_coordinate

end Normal

universe u

variable (k : Type u) {H B R V : Type u} [CommRing k]
  [CommRing H] [CommRing B] [CommRing R] [CommRing V]
  [Algebra k H] [Algebra k B] [Algebra k R] [Algebra k V]
  [Algebra H B] [Algebra H R] [Algebra H V] [Algebra B V]
  [IsScalarTower k H R] [IsScalarTower k B V] [IsScalarTower H B V]
  [Algebra H[X] R] [IsScalarTower H H[X] R] [Algebra.Etale H[X] R]
  [Algebra B[X] V] [IsScalarTower B B[X] V] [Algebra.Etale B[X] V]
  [Algebra.Smooth k R]

/-- Refinement of the coefficient ring preserves the interval using the
actual new normal derivative and the original ground field. -/
theorem etaleLine_coefficient_interval_refinement {ι : Type*}
    (f : R →ₐ[k] V) (hf : f.toRingHom.Etale)
    (hcoeff : ∀ h : H, f (algebraMap H R h) = algebraMap H V h)
    (hcoord : f (algebraMap H[X] R X) = algebraMap B[X] V X)
    (p : ι → R) (b : ℕ) (C : Ideal (R ⧸ Ideal.span {algebraMap H[X] R X}))
    (hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal
      (CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := H) (R := R))
      (algebraMap H[X] R X) p b ≤ C)
    (hupp : C ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (algebraMap H[X] R X) (Ideal.span (Set.range p)) b) :
    WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal
        (CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := B) (R := V))
        (f (algebraMap H[X] R X)) (fun i => f (p i)) b ≤
      C.map (Relative.CoefficientBaseChange.Construction.mappedHypersurfaceQuotientMap f.toRingHom (algebraMap H[X] R X)) ∧
    C.map (Relative.CoefficientBaseChange.Construction.mappedHypersurfaceQuotientMap f.toRingHom (algebraMap H[X] R X)) ≤
      Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (f (algebraMap H[X] R X))
        (Ideal.span (Set.range (fun i => f (p i)))) b := by
  let fH : R →ₐ[H] V := { f.toRingHom with commutes' := hcoeff }
  have hnormal (x : R) : CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := B) (R := V) (f x) =
      f (CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := H) (R := R) x) :=
    etaleLine_normalDerivation_coefficient_refinement fH hcoord x
  exact Blowups.Smooth.CoefficientNaturality.Construction.smooth_coefficient_family_interval_map k f hf
    (CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := H) (R := R))
    (CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := B) (R := V)) hnormal
    (algebraMap H[X] R X) p b C hlow hupp

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.CoefficientRefinementTransport.Construction
