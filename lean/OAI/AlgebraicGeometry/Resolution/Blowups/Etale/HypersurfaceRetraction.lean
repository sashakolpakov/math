import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.PolynomialFiber
import OAI.AlgebraicGeometry.Resolution.Blowups.UnramifiedQuotientSection
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ComparisonFiberProduct

/-! # Hypersurface Retraction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.HypersurfaceRetraction.Construction

noncomputable section

/-! An étale ambient refinement with a retraction onto its coordinate hypersurface. -/

open _root_.Polynomial
open scoped TensorProduct

universe u

variable (A R : Type u) [CommRing A] [CommRing R] [Algebra A R]
  [Algebra A[X] R] [IsScalarTower A A[X] R]

abbrev etaleCoordinateFiber := R ⧸ Ideal.span {algebraMap A[X] R (X : A[X])}

local instance coordinateFiberPolynomialAlgebra : Algebra A[X] (etaleCoordinateFiber A R)[X] :=
  Polynomial.algebra A (etaleCoordinateFiber A R)

local instance coordinateFiberPolynomialSMul : SMul A[X] (etaleCoordinateFiber A R)[X] :=
  (coordinateFiberPolynomialAlgebra A R).toSMul

local instance coordinateFiberPolynomialModule : Module A[X] (etaleCoordinateFiber A R)[X] :=
  Algebra.toModule

local instance coordinateFiberPolynomialSelfTower :
    IsScalarTower A[X] A[X] (etaleCoordinateFiber A R)[X] :=
  IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro p
    simp [Polynomial.algebraMap_def])

abbrev etaleCoordinateRetractionRing :=
  (etaleCoordinateFiber A R)[X] ⊗[A[X]] R

/-- Evaluation at the zero coordinate respects the original coordinate algebra. -/
def etaleCoordinateFiberPolynomialEval :
    (etaleCoordinateFiber A R)[X] →ₐ[A[X]] etaleCoordinateFiber A R where
  __ := Polynomial.evalRingHom 0
  commutes' p := by
    have h : (Polynomial.evalRingHom (0 : etaleCoordinateFiber A R)).comp
        (algebraMap A[X] (etaleCoordinateFiber A R)[X]) =
          algebraMap A[X] (etaleCoordinateFiber A R) := by
      apply Polynomial.ringHom_ext
      · intro a
        change Polynomial.eval 0 (Polynomial.map (algebraMap A (etaleCoordinateFiber A R)) (C a)) =
          algebraMap A[X] (etaleCoordinateFiber A R) (C a)
        rw [Polynomial.map_C, eval_C]
        exact IsScalarTower.algebraMap_apply A A[X] (etaleCoordinateFiber A R) a
      · change Polynomial.eval 0 (Polynomial.map (algebraMap A (etaleCoordinateFiber A R)) X) =
          Ideal.Quotient.mk _ (algebraMap A[X] R X)
        rw [Polynomial.map_X, eval_X]
        exact (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)).symm
    exact RingHom.congr_fun h p

/-- The actual tensor-product ambient ring retracts onto the original hypersurface. -/
def etaleCoordinateRetraction : etaleCoordinateRetractionRing A R →ₐ[etaleCoordinateFiber A R]
    etaleCoordinateFiber A R where
  __ := (Algebra.TensorProduct.lift (etaleCoordinateFiberPolynomialEval A R)
    (IsScalarTower.toAlgHom A[X] R (etaleCoordinateFiber A R))
    (fun _ _ => Commute.all _ _)).toRingHom
  commutes' h := by
    change Polynomial.eval 0 (C h) * 1 = h
    rw [eval_C, mul_one]

theorem etaleCoordinateRetraction_right (r : R) :
    etaleCoordinateRetraction A R
      ((Algebra.TensorProduct.includeRight : R →ₐ[A[X]] etaleCoordinateRetractionRing A R) r) =
        Ideal.Quotient.mk _ r := by
  change etaleCoordinateFiberPolynomialEval A R 1 *
    Ideal.Quotient.mk (Ideal.span {algebraMap A[X] R (X : A[X])}) r = _
  rw [map_one, one_mul]

theorem etaleCoordinateRetraction_coordinate :
    etaleCoordinateRetraction A R
      (algebraMap (etaleCoordinateFiber A R)[X] (etaleCoordinateRetractionRing A R) X) = 0 := by
  change Polynomial.eval 0 (X : (etaleCoordinateFiber A R)[X]) * 1 = 0
  rw [eval_X, zero_mul]

variable [Algebra.Etale A[X] R]

instance etaleCoordinateFiber_etale : Algebra.Etale A (etaleCoordinateFiber A R) :=
  PolynomialFiber.Construction.etale_polynomial_zero_fiber

instance etaleCoordinateRetractionRing_etale :
    Algebra.Etale (etaleCoordinateFiber A R)[X] (etaleCoordinateRetractionRing A R) :=
  inferInstanceAs (Algebra.Etale (etaleCoordinateFiber A R)[X]
    ((etaleCoordinateFiber A R)[X] ⊗[A[X]] R))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ambient refinement is étale over the original ambient ring as well. -/
theorem etaleCoordinateRetractionRing_right_etale :
    RingHom.Etale (R := R) (S := etaleCoordinateRetractionRing A R)
      (Algebra.TensorProduct.includeRight : R →ₐ[A[X]] etaleCoordinateRetractionRing A R).toRingHom := by
  let : Algebra.Etale A[X] (etaleCoordinateFiber A R)[X] := PolynomialFiber.Construction.etale_polynomial_coefficient_extension
  exact ComparisonFiberProduct.Construction.etaleComparisonRight_etale (k := A[X]) (P := A[X])
    (R := (etaleCoordinateFiber A R)[X]) (S := R)

omit [IsScalarTower A A[X] R] [Algebra.Etale A[X] R] in
theorem etaleCoordinateRetractionRing_coordinate :
    (Algebra.TensorProduct.includeRight : R →ₐ[A[X]] etaleCoordinateRetractionRing A R)
      (algebraMap A[X] R X) =
        algebraMap (etaleCoordinateFiber A R)[X] (etaleCoordinateRetractionRing A R) X := by
  rw [AlgHom.commutes,
    IsScalarTower.algebraMap_apply A[X] (etaleCoordinateFiber A R)[X] (etaleCoordinateRetractionRing A R)]
  change algebraMap (etaleCoordinateFiber A R)[X] (etaleCoordinateRetractionRing A R)
    (Polynomial.map (algebraMap A (etaleCoordinateFiber A R)) X) = _
  rw [Polynomial.map_X]

omit [Algebra.Etale A[X] R] in
theorem etaleCoordinateRetractionRing_constants (a : A) :
    (Algebra.TensorProduct.includeRight : R →ₐ[A[X]] etaleCoordinateRetractionRing A R)
      (algebraMap A R a) = algebraMap (etaleCoordinateFiber A R) (etaleCoordinateRetractionRing A R)
        (algebraMap A (etaleCoordinateFiber A R) a) := by
  rw [IsScalarTower.algebraMap_apply A A[X] R, AlgHom.commutes]
  exact (IsScalarTower.algebraMap_apply A A[X] (etaleCoordinateRetractionRing A R) a).symm.trans
    (IsScalarTower.algebraMap_apply A (etaleCoordinateFiber A R) (etaleCoordinateRetractionRing A R) a)

/-- Refine the ambient scheme étale-locally so that its coordinate
hypersurface is the original fiber and the ambient ring is étale over the
polynomial line over that fiber. The quotient map is preserved exactly. -/
theorem exists_etale_hypersurface_retraction_neighborhood :
    ∃ (V : Type u) (_ : CommRing V) (_ : Algebra (etaleCoordinateFiber A R) V)
      (_ : Algebra (etaleCoordinateFiber A R)[X] V),
      IsScalarTower (etaleCoordinateFiber A R) (etaleCoordinateFiber A R)[X] V ∧
      Algebra.Etale (etaleCoordinateFiber A R)[X] V ∧
      ∃ g : R →+* V, g.Etale ∧
        g (algebraMap A[X] R X) = algebraMap (etaleCoordinateFiber A R)[X] V X ∧
        (∀ a : A, g (algebraMap A R a) = algebraMap (etaleCoordinateFiber A R) V
          (algebraMap A (etaleCoordinateFiber A R) a)) ∧
        ∃ e : (V ⧸ Ideal.span {g (algebraMap A[X] R X)}) ≃ₐ[etaleCoordinateFiber A R]
          etaleCoordinateFiber A R,
          e.toRingHom.comp ((Ideal.Quotient.mk (Ideal.span {g (algebraMap A[X] R X)})).comp g) =
            Ideal.Quotient.mk (Ideal.span {algebraMap A[X] R (X : A[X])}) := by
  let H := etaleCoordinateFiber A R
  let U := etaleCoordinateRetractionRing A R
  let : CommRing U := inferInstanceAs (CommRing (etaleCoordinateRetractionRing A R))
  let z := algebraMap H[X] U (X : H[X])
  let Z : Ideal U := Ideal.span {z}
  let r : U →ₐ[H] H := etaleCoordinateRetraction A R
  have hZ : Z ≤ RingHom.ker r := by
    apply Ideal.span_le.mpr
    rintro _ ⟨rfl⟩
    exact etaleCoordinateRetraction_coordinate A R
  let : Algebra.Etale H (U ⧸ Z) := PolynomialFiber.Construction.etale_polynomial_zero_fiber
  obtain ⟨s, ε, hs, hε⟩ := UnramifiedQuotientSection.Construction.exists_unramified_quotient_section_neighborhood Z r hZ
  let V := Localization.Away s
  let η : U →+* V := algebraMap U V
  let g₀ : R →+* U :=
    (Algebra.TensorProduct.includeRight : R →ₐ[A[X]] etaleCoordinateRetractionRing A R).toRingHom
  let g := η.comp g₀
  have hg₀ : g₀.Etale := etaleCoordinateRetractionRing_right_etale A R
  have hη : η.Etale := RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway s)
  have hcoord : g₀ (algebraMap A[X] R X) = z := etaleCoordinateRetractionRing_coordinate A R
  have hZI : Z.map η = Ideal.span {g (algebraMap A[X] R X)} := by
    dsimp only [Z]
    rw [Ideal.map_span, Set.image_singleton]
    congr 1
    rw [← hcoord]
    rfl
  let e : (V ⧸ Ideal.span {g (algebraMap A[X] R X)}) ≃ₐ[H] H :=
    (Ideal.quotientEquivAlgOfEq H hZI.symm).trans ε
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    g, RingHom.Etale.stableUnderComposition g₀ η hg₀ hη, ?_, ?_, e, ?_⟩
  · change η (g₀ (algebraMap A[X] R X)) = algebraMap H[X] V X
    rw [hcoord]
    exact (IsScalarTower.algebraMap_apply H[X] U V (X : H[X])).symm
  · intro a
    change η (g₀ (algebraMap A R a)) = algebraMap H V (algebraMap A H a)
    have hc : g₀ (algebraMap A R a) = algebraMap H U (algebraMap A H a) :=
      etaleCoordinateRetractionRing_constants A R a
    rw [hc]
    exact (IsScalarTower.algebraMap_apply H U V (algebraMap A H a)).symm
  · apply RingHom.ext
    intro a
    change ε (Ideal.quotientEquivAlgOfEq H hZI.symm
      (Ideal.Quotient.mk (Ideal.span {g (algebraMap A[X] R X)}) (g a))) = _
    rw [Ideal.quotientEquivAlgOfEq_mk]
    exact (RingHom.congr_fun hε (g₀ a)).trans (etaleCoordinateRetraction_right A R a)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.HypersurfaceRetraction.Construction
