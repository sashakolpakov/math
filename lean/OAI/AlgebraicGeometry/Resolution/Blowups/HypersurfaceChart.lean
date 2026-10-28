import OAI.AlgebraicGeometry.Resolution.Blowups.OrderLocus
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Hypersurface Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfaceChart.Construction

noncomputable section

/-! Smooth affine charts of derivative hypersurfaces used in Blowups. -/

open _root_.MvPolynomial _root_.Algebra

universe u

/-- Localizing a finite presentation at its chosen Jacobian minor makes
the presented algebra smooth. -/
theorem preSubmersive_smooth_of_localization
    {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S] [Finite ι] [Finite σ]
    (P : PreSubmersivePresentation R S ι σ) (L : Type*) [CommRing L]
    [Algebra S L] [Algebra R L] [IsScalarTower R S L] [IsLocalization.Away P.jacobian L] :
    Algebra.Smooth R L := by
  let Q : PreSubmersivePresentation S L Unit Unit :=
    PreSubmersivePresentation.localizationAway L P.jacobian
  have hu : IsUnit (algebraMap S L P.jacobian) :=
    IsLocalization.Away.algebraMap_isUnit P.jacobian
  let P' : SubmersivePresentation R L (Unit ⊕ ι) (Unit ⊕ σ) :=
    { toPreSubmersivePresentation := Q.comp P
      jacobian_isUnit := by
        rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian]
        rw [Algebra.smul_def, PreSubmersivePresentation.localizationAway_jacobian]
        exact hu.mul hu }
  let : Algebra.IsStandardSmooth R L := P'.isStandardSmooth
  infer_instance

variable {K ι : Type*} [CommRing K]

/-- The actual coordinate ring of a polynomial hypersurface. -/
abbrev hypersurfaceRing (q : MvPolynomial ι K) := MvPolynomial ι K ⧸ Ideal.span {q}

/-- The standard presentation of a hypersurface, choosing one variable
for its one-by-one Jacobian minor. -/
def hypersurfacePreSubmersive (q : MvPolynomial ι K) (i : ι) :
    PreSubmersivePresentation K (hypersurfaceRing q) ι Unit where
  toGenerators := Generators.ofAlgHom (Ideal.Quotient.mkₐ K (Ideal.span {q}))
    (Ideal.Quotient.mkₐ_surjective K (Ideal.span {q}))
  relation _ := q
  span_range_relation_eq_ker := by
    rw [Generators.ker_ofAlgHom]
    simp only [Set.range_const]
    exact Ideal.mk_ker.symm
  map _ := i
  map_inj := fun _ _ _ => Subsingleton.elim _ _

/-- The selected Jacobian minor for one hypersurface equation is its
partial derivative in the selected variable. -/
theorem hypersurfacePreSubmersive_jacobian (q : MvPolynomial ι K) (i : ι) :
    (hypersurfacePreSubmersive q i).jacobian =
      Ideal.Quotient.mk (Ideal.span {q}) (pderiv i q) := by
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_unique,
    PreSubmersivePresentation.jacobiMatrix_apply]
  rw [Generators.algebraMap_apply]
  change aeval ((Ideal.Quotient.mkₐ K (Ideal.span {q})) ∘ X) (pderiv i q) = _
  rw [← aeval_unique (Ideal.Quotient.mkₐ K (Ideal.span {q}))]
  rfl

/-- The open hypersurface chart where a chosen partial derivative is invertible. -/
abbrev hypersurfaceDerivativeChart (q : MvPolynomial ι K) (i : ι) :=
  Localization.Away (Ideal.Quotient.mk (Ideal.span {q}) (pderiv i q))

/-- A hypersurface is smooth wherever one of its partial derivatives is invertible. -/
theorem hypersurfaceDerivativeChart_smooth [Finite ι] (q : MvPolynomial ι K) (i : ι) :
    Algebra.Smooth K (hypersurfaceDerivativeChart q i) := by
  let : IsLocalization.Away (hypersurfacePreSubmersive q i).jacobian
      (hypersurfaceDerivativeChart q i) := by
    rw [hypersurfacePreSubmersive_jacobian]
    infer_instance
  exact preSubmersive_smooth_of_localization (hypersurfacePreSubmersive q i)
    (hypersurfaceDerivativeChart q i)

/-- The corresponding affine hypersurface chart is a smooth scheme over its base. -/
theorem hypersurfaceDerivativeChart_scheme_smooth
    {K ι : Type u} [CommRing K] [Finite ι] (q : MvPolynomial ι K) (i : ι) :
    AlgebraicGeometry.Smooth
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K (hypersurfaceDerivativeChart q i)))) := by
  rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)]
  exact RingHom.smooth_algebraMap.mpr (hypersurfaceDerivativeChart_smooth q i)

/-- Evaluation at a point satisfying the hypersurface equation descends to its quotient ring. -/
def hypersurfaceEval (q : MvPolynomial ι K) (a : ι → K) (hq : eval a q = 0) :
    hypersurfaceRing q →+* K :=
  Ideal.Quotient.lift (Ideal.span {q}) (eval a) (by
    change Ideal.span {q} ≤ RingHom.ker (eval a)
    apply Ideal.span_le.mpr
    intro p hp
    obtain rfl := Set.mem_singleton_iff.mp hp
    exact hq)

@[simp]
theorem hypersurfaceEval_mk (q : MvPolynomial ι K) (a : ι → K) (hq : eval a q = 0)
    (p : MvPolynomial ι K) :
    hypersurfaceEval q a hq (Ideal.Quotient.mk (Ideal.span {q}) p) = eval a p := rfl

/-- A point with nonvanishing chosen derivative lifts to the smooth hypersurface chart. -/
def hypersurfaceChartEval {K ι : Type*} [Field K]
    (q : MvPolynomial ι K) (i : ι) (a : ι → K)
    (hq : eval a q = 0) (hi : eval a (pderiv i q) ≠ 0) :
    hypersurfaceDerivativeChart q i →+* K :=
  IsLocalization.Away.lift (g := hypersurfaceEval q a hq)
    (Ideal.Quotient.mk (Ideal.span {q}) (pderiv i q))
    (by rw [hypersurfaceEval_mk]; exact isUnit_iff_ne_zero.mpr hi)

/-- The lifted chart point has exactly the original polynomial coordinates. -/
theorem hypersurfaceChartEval_coordinates {K ι : Type*} [Field K]
    (q : MvPolynomial ι K) (i : ι) (a : ι → K)
    (hq : eval a q = 0) (hi : eval a (pderiv i q) ≠ 0) (p : MvPolynomial ι K) :
    hypersurfaceChartEval q i a hq hi
      (algebraMap (hypersurfaceRing q) (hypersurfaceDerivativeChart q i)
        (Ideal.Quotient.mk (Ideal.span {q}) p)) = eval a p := by
  unfold hypersurfaceChartEval
  rw [IsLocalization.Away.lift_eq, hypersurfaceEval_mk]

/-- A derivative equation containing the high-order locus has a smooth
affine hypersurface chart at the chosen point, with its point and polynomial
coordinates explicitly supplied. -/
theorem exists_smooth_derivative_hypersurface
    {K ι : Type*} [Field K] [CharZero K] [Finite ι]
    (J : Ideal (MvPolynomial ι K)) (a : ι → K) (n : ℕ)
    (hJ : J ≤ PolynomialTranslation.Construction.polynomialPointIdeal a ^ (n + 1))
    (hJ1 : ¬ J ≤ PolynomialTranslation.Construction.polynomialPointIdeal a ^ (n + 2)) :
    ∃ (p : J) (l : List ι) (i : ι),
      let q := DifferentialOrder.Construction.iteratedPDeriv l p.val
      l.length = n ∧ eval a q = 0 ∧ eval a (pderiv i q) ≠ 0 ∧
      Algebra.Smooth K (hypersurfaceDerivativeChart q i) ∧
      (∃ e : hypersurfaceDerivativeChart q i →+* K,
        ∀ r : MvPolynomial ι K,
          e (algebraMap (hypersurfaceRing q) (hypersurfaceDerivativeChart q i)
            (Ideal.Quotient.mk (Ideal.span {q}) r)) = eval a r) ∧
      ∀ y : ι → K, J ≤ PolynomialTranslation.Construction.polynomialPointIdeal y ^ (n + 1) → eval y q = 0 := by
  obtain ⟨p, l, i, hl, hz, hi, hcontains⟩ :=
    OrderLocus.Construction.exists_gradient_equation_containing_orderLocus J a n hJ hJ1
  refine ⟨p, l, i, hl, hz, hi, hypersurfaceDerivativeChart_smooth _ _, ?_, hcontains⟩
  exact ⟨hypersurfaceChartEval _ i a hz hi,
    hypersurfaceChartEval_coordinates _ i a hz hi⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfaceChart.Construction
