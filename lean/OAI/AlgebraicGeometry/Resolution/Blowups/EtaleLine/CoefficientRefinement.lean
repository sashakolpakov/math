import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.HypersurfaceRetraction
import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.RetractionStep

/-! # Coefficient Refinement -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.CoefficientRefinement.Construction

noncomputable section

/-! Actual ambient refinements over an étale refinement of the retained coefficient ring. -/

open _root_.Polynomial
open scoped TensorProduct

universe u

variable {H B R : Type u} [CommRing H] [CommRing B] [CommRing R]
  [Algebra H B] [Algebra H R] [Algebra H[X] R] [IsScalarTower H H[X] R]

local instance lineRefinementPolynomialAlgebra : Algebra H[X] B[X] := Polynomial.algebra H B
local instance lineRefinementPolynomialSMul : SMul H[X] B[X] :=
  (lineRefinementPolynomialAlgebra (H := H) (B := B)).toSMul
local instance lineRefinementPolynomialModule : Module H[X] B[X] := Algebra.toModule
local instance lineRefinementPolynomialTower : IsScalarTower H H[X] B[X] :=
  IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro h
    simp [Polynomial.algebraMap_def])

abbrev etaleLineCoefficientRefinementRing := B[X] ⊗[H[X]] R

def etaleLineCoefficientRefinementRetraction
    (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H) :
    etaleLineCoefficientRefinementRing (H := H) (B := B) (R := R) →ₐ[B] B := by
  let l : B[X] →ₐ[H] B := (Polynomial.aeval (0 : B)).restrictScalars H
  let r : R →ₐ[H] B := (Algebra.ofId H B).comp
    (e.toAlgHom.comp (Ideal.Quotient.mkₐ H (Ideal.span {algebraMap H[X] R X})))
  have h : ∀ p : H[X], l (algebraMap H[X] B[X] p) = r (algebraMap H[X] R p) := by
    change ∀ p, (l.toRingHom.comp (algebraMap H[X] B[X])) p =
      (r.toRingHom.comp (algebraMap H[X] R)) p
    apply RingHom.congr_fun
    apply Polynomial.ringHom_ext
    · intro a
      change Polynomial.aeval (0 : B) (Polynomial.map (algebraMap H B) (C a)) =
        r (algebraMap H[X] R (algebraMap H H[X] a))
      rw [Polynomial.map_C, Polynomial.aeval_C, ← IsScalarTower.algebraMap_apply H H[X] R,
        r.commutes]
      rfl
    · change Polynomial.aeval (0 : B) (Polynomial.map (algebraMap H B) X) =
        algebraMap H B (e (Ideal.Quotient.mk (Ideal.span {algebraMap H[X] R X})
          (algebraMap H[X] R X)))
      rw [Polynomial.map_X, Polynomial.aeval_X,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero, map_zero]
  refine { (Blowups.Etale.ComparisonFiberProduct.Construction.etaleComparisonPoint l r h).toRingHom with commutes' := ?_ }
  intro b
  change l (C b) * r 1 = b
  rw [map_one, mul_one]
  exact Polynomial.aeval_C (0 : B) b

theorem etaleLineCoefficientRefinementRetraction_right
    (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H) (x : R) :
    etaleLineCoefficientRefinementRetraction (B := B) e
      ((Algebra.TensorProduct.includeRight : R →ₐ[H[X]]
        etaleLineCoefficientRefinementRing (H := H) (B := B) (R := R)) x) =
      algebraMap H B (e (Ideal.Quotient.mk (Ideal.span {algebraMap H[X] R X}) x)) := by
  change Polynomial.aeval (0 : B) (1 : B[X]) * _ = _
  rw [map_one, one_mul]
  rfl

theorem etaleLineCoefficientRefinementRetraction_coordinate
    (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H) :
    etaleLineCoefficientRefinementRetraction (B := B) e
      (algebraMap B[X] (etaleLineCoefficientRefinementRing (H := H) (B := B) (R := R)) X) = 0 := by
  change Polynomial.aeval (0 : B) X * _ = 0
  rw [Polynomial.aeval_X, zero_mul]

omit [Algebra H R] [IsScalarTower H H[X] R] in
theorem etaleLineCoefficientRefinementRing_coordinate :
    (Algebra.TensorProduct.includeRight : R →ₐ[H[X]]
      etaleLineCoefficientRefinementRing (H := H) (B := B) (R := R)) (algebraMap H[X] R X) =
      algebraMap B[X] (etaleLineCoefficientRefinementRing (H := H) (B := B) (R := R)) X := by
  rw [AlgHom.commutes,
    IsScalarTower.algebraMap_apply H[X] B[X] (etaleLineCoefficientRefinementRing (H := H) (B := B) (R := R))]
  change algebraMap B[X] _ (Polynomial.map (algebraMap H B) X) = _
  rw [Polynomial.map_X]

theorem etaleLineCoefficientRefinementRing_constants (h : H) :
    (Algebra.TensorProduct.includeRight : R →ₐ[H[X]]
      etaleLineCoefficientRefinementRing (H := H) (B := B) (R := R)) (algebraMap H R h) =
      algebraMap B (etaleLineCoefficientRefinementRing (H := H) (B := B) (R := R))
        (algebraMap H B h) := by
  rw [IsScalarTower.algebraMap_apply H H[X] R, AlgHom.commutes]
  exact (IsScalarTower.algebraMap_apply H H[X] _ h).symm.trans
    (IsScalarTower.algebraMap_apply H B _ h)

variable [Algebra.Etale H B] [Algebra.Etale H[X] R]

omit [Algebra.Etale H[X] R] in
theorem etaleLineCoefficientRefinementRing_right_etale :
    (Algebra.TensorProduct.includeRight : R →ₐ[H[X]]
      etaleLineCoefficientRefinementRing (H := H) (B := B) (R := R)).toRingHom.Etale := by
  let : Algebra.Etale H[X] B[X] := Blowups.Etale.PolynomialFiber.Construction.etale_polynomial_coefficient_extension
  exact Blowups.Etale.ComparisonFiberProduct.Construction.etaleComparisonRight_etale (k := H) (P := H[X]) (R := B[X]) (S := R)

/-- Any étale coefficient refinement lifts to an actual étale ambient
refinement with a retraction, preserving the original quotient map exactly. -/
theorem exists_etale_line_coefficient_refinement
    (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H) :
    ∃ (V : Type u) (_ : CommRing V) (_ : Algebra B V) (_ : Algebra B[X] V),
      IsScalarTower B B[X] V ∧ Algebra.Etale B[X] V ∧
      ∃ f : R →+* V, f.Etale ∧ f (algebraMap H[X] R X) = algebraMap B[X] V X ∧
        (∀ h : H, f (algebraMap H R h) = algebraMap B V (algebraMap H B h)) ∧
        ∃ e' : (V ⧸ Ideal.span {f (algebraMap H[X] R X)}) ≃ₐ[B] B,
          e'.toRingHom.comp ((Ideal.Quotient.mk (Ideal.span {f (algebraMap H[X] R X)})).comp f) =
            (algebraMap H B).comp (e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap H[X] R X}))) := by
  let U := etaleLineCoefficientRefinementRing (H := H) (B := B) (R := R)
  let : CommRing U := inferInstanceAs
    (CommRing (etaleLineCoefficientRefinementRing (H := H) (B := B) (R := R)))
  let : Algebra.Etale B[X] U := inferInstanceAs (Algebra.Etale B[X] (B[X] ⊗[H[X]] R))
  let z := algebraMap B[X] U (X : B[X])
  let Z : Ideal U := Ideal.span {z}
  let r : U →ₐ[B] B := etaleLineCoefficientRefinementRetraction e
  have hZ : Z ≤ RingHom.ker r := by
    apply Ideal.span_le.mpr
    rintro _ ⟨rfl⟩
    exact etaleLineCoefficientRefinementRetraction_coordinate e
  let hEtale : Algebra.Etale B (U ⧸ Z) := Blowups.Etale.PolynomialFiber.Construction.etale_polynomial_zero_fiber
  let : Algebra.FinitePresentation B (U ⧸ Z) := hEtale.finitePresentation
  let : Algebra.FiniteType B (U ⧸ Z) := Algebra.FiniteType.of_finitePresentation
  let : Algebra.EssFiniteType B (U ⧸ Z) := inferInstance
  obtain ⟨s, ε, _, hε⟩ := UnramifiedQuotientSection.Construction.exists_unramified_quotient_section_neighborhood Z r hZ
  let V := Localization.Away s
  let η : U →+* V := algebraMap U V
  let f₀ : R →+* U := (Algebra.TensorProduct.includeRight : R →ₐ[H[X]] U).toRingHom
  let f := η.comp f₀
  have hf₀ : f₀.Etale := etaleLineCoefficientRefinementRing_right_etale
  have hη : η.Etale := RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway s)
  have hcoord : f₀ (algebraMap H[X] R X) = z := etaleLineCoefficientRefinementRing_coordinate
  have hZI : Z.map η = Ideal.span {f (algebraMap H[X] R X)} := by
    dsimp only [Z]
    rw [Ideal.map_span, Set.image_singleton]
    congr 1
    rw [← hcoord]
    rfl
  let e' : (V ⧸ Ideal.span {f (algebraMap H[X] R X)}) ≃ₐ[B] B :=
    (Ideal.quotientEquivAlgOfEq B hZI.symm).trans ε
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    f, RingHom.Etale.stableUnderComposition f₀ η hf₀ hη, ?_, ?_, e', ?_⟩
  · change η (f₀ (algebraMap H[X] R X)) = algebraMap B[X] V X
    rw [hcoord]
    exact (IsScalarTower.algebraMap_apply B[X] U V X).symm
  · intro h
    change η (f₀ (algebraMap H R h)) = algebraMap B V (algebraMap H B h)
    have hc : f₀ (algebraMap H R h) = algebraMap B U (algebraMap H B h) :=
      etaleLineCoefficientRefinementRing_constants h
    rw [hc]
    exact (IsScalarTower.algebraMap_apply B U V (algebraMap H B h)).symm
  · apply RingHom.ext
    intro x
    change ε (Ideal.quotientEquivAlgOfEq B hZI.symm
      (Ideal.Quotient.mk (Ideal.span {f (algebraMap H[X] R X)}) (f x))) = _
    rw [Ideal.quotientEquivAlgOfEq_mk]
    exact (RingHom.congr_fun hε (f₀ x)).trans (etaleLineCoefficientRefinementRetraction_right e x)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.CoefficientRefinement.Construction
