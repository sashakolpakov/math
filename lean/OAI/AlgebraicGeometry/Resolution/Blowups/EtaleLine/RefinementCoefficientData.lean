import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.RefinementReferenceBase
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialMap

/-! # Refinement Coefficient Data -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.RefinementCoefficientData.Construction

noncomputable section

/-! All recursive coefficient data on an actual coefficient-ring refinement. -/

open _root_.Polynomial _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) {H B R : Type u} [CommRing k] [CommRing H] [CommRing B] [CommRing R]
  [Algebra k H] [Algebra k B] [Algebra k R] [Algebra H R] [IsScalarTower k H R]
  [Algebra H[X] R] [IsScalarTower H H[X] R] [Algebra.Etale H[X] R]
  [Algebra.Smooth k R]

/-- An étale refinement of the coefficient algebra reconstructs every
recursive hypothesis in the new polynomial coordinate: smooth ambient ring,
exact retained coefficient ideal, its two interval bounds, and maximal contact. -/
theorem exists_etale_line_refined_coefficient_data {ι : Type u}
    (φ : H →ₐ[k] B) (hφ : φ.toRingHom.Etale)
    (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H)
    (p : ι → R) (n : ℕ) (C : Ideal (R ⧸ Ideal.span {algebraMap H[X] R X}))
    (hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal
      (Retracted.CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := H) (R := R))
      (algebraMap H[X] R X) p (n + 1) ≤ C)
    (hupp : C ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (algebraMap H[X] R X) (Ideal.span (Set.range p)) (n + 1))
    (hz : algebraMap H[X] R X ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Ideal.span (Set.range p)) n) :
    ∃ (V : CommRingCat.{u}) (_ : Algebra k V) (_ : Algebra B V) (_ : Algebra B[X] V)
      (_ : IsScalarTower k B V) (_ : IsScalarTower B B[X] V)
      (_ : Algebra.Etale B[X] V) (_ : Algebra.Smooth k V),
      ∃ f : R →ₐ[k] V, f.toRingHom.Etale ∧
        f (algebraMap H[X] R X) = algebraMap B[X] V X ∧
        ∃ (e' : (V ⧸ Ideal.span {algebraMap B[X] V X}) ≃ₐ[B] B)
          (C' : Ideal (V ⧸ Ideal.span {algebraMap B[X] V X})),
          WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal
            (Retracted.CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := B) (R := V))
            (algebraMap B[X] V X) (fun i => f (p i)) (n + 1) ≤ C' ∧
          C' ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (algebraMap B[X] V X)
            (Ideal.span (Set.range (fun i => f (p i)))) (n + 1) ∧
          C'.map e'.toRingHom = (C.map e.toRingHom).map φ.toRingHom ∧
          algebraMap B[X] V X ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
            (Ideal.span (Set.range (fun i => f (p i)))) n ∧
          e'.toRingHom.comp ((Ideal.Quotient.mk (Ideal.span {algebraMap B[X] V X})).comp f.toRingHom) =
            φ.toRingHom.comp (e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap H[X] R X}))) := by
  obtain ⟨V, akV, aBV, aBPV, hkBV, hBPV, heV, hsmV, f, hf, hcoord, hcoeff, e', hcomm⟩ :=
    RefinementReferenceBase.Construction.exists_etale_line_original_base_refinement k φ hφ e
  let : Algebra H B := φ.toRingHom.toAlgebra
  let : Algebra H V := ((algebraMap B V).comp φ.toRingHom).toAlgebra
  let : IsScalarTower H B V := IsScalarTower.of_algebraMap_eq' rfl
  have hinterval := Retracted.CoefficientRefinementTransport.Construction.etaleLine_coefficient_interval_refinement k f hf hcoeff hcoord
    p (n + 1) C hlow hupp
  have hp : (Ideal.span (Set.range p)).map f.toRingHom =
      Ideal.span (Set.range (fun i => f (p i))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hz' := Ideal.mem_map_of_mem f.toRingHom hz
  rw [Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k f hf _ n, hp] at hz'
  refine ⟨V, akV, aBV, aBPV, hkBV, hBPV, heV, hsmV, f, hf, hcoord, ?_⟩
  rw [← hcoord]
  exact ⟨e', C.map (Relative.CoefficientBaseChange.Construction.mappedHypersurfaceQuotientMap f.toRingHom (algebraMap H[X] R X)),
    hinterval.1, hinterval.2,
    Retracted.CoefficientRefinementTransport.Construction.retracted_coefficient_refinement_map f.toRingHom φ.toRingHom (algebraMap H[X] R X)
      e.toRingEquiv e'.toRingEquiv hcomm C,
    hz', hcomm⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.RefinementCoefficientData.Construction
