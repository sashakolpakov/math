import OAI.Geometry.ComplexTorus.RiemannProjectivity.PointwiseRegular
import OAI.Geometry.ComplexTorus.RiemannProjectivity.SeparatingLinearCoordinates
import OAI.Geometry.ComplexTorus.RiemannProjectivity.RegularCoordinate
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity
import OAI.AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints
import Mathlib.RingTheory.Algebraic.Integral

/-! # Jacobian Localization At -/

namespace OAI

noncomputable section

namespace Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt.Constructions.RegularConeEquations

/-! # RiemannProjectivity: independent algebraic equations at every normalized period-cone point -/

open Set _root_.Polynomial
open OAI.AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent OAI.Geometry.ComplexTorus.RiemannProjectivity.SeparatingLinearCoordinates.Constructions.SeparatingFiberCoordinates

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  {n : ℕ}

theorem exists_at_parameter (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Topology.IsClosedEmbedding f)
    (hd : ∀ (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z))
    (i : Fin (n + 1)) (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E)
    (hi : f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source)
    (v : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))
    (hv : v.val = ConeTangentF.Constructions.ConeTangent.parameterization i (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) (z, 1)) :
    ∃ (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) + 1) → ℂ))
      (m : ℕ) (e : (Fin (n + 1) → ℂ) ≃L[ℂ]
        ((Fin (Module.finrank ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) + 1) → ℂ) × (Fin m → ℂ)))
      (F : Fin m → Polynomial (MvPolynomial (Fin (Module.finrank ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) + 1)) ℂ)),
      (∀ w, (e w).1 = L w) ∧
      BranchCoefficientsAt.Constructions.BranchCoefficients.HasHolomorphicInverseAt
        (Subtype.val : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) → (Fin (n + 1) → ℂ))
        (fun w => L w) v ∧
      (∀ j, F j ≠ 0) ∧
      (∀ j, ((F j).map (MvPolynomial.eval (L v))).derivative.eval (SeparatingLinearCoordinates.Constructions.SeparatingFiberCoordinates.coordinate e j v) ≠ 0) ∧
      ∀ j w, w ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) →
        (F j).eval₂ (MvPolynomial.eval (L w)) (SeparatingLinearCoordinates.Constructions.SeparatingFiberCoordinates.coordinate e j w) = 0 := by
  classical
  obtain ⟨L, hker, hp, hs, hfinite, hInv⟩ :=
    PointwiseRegular.Constructions.PointwiseRegularProjection.exists_at_parameter Φ f hf hd i z hi v hv
  have hLs : Function.Surjective L := fun y => by
    obtain ⟨w, hw⟩ := hs y
    exact ⟨w, hw⟩
  obtain ⟨m, e, he, hsep⟩ := SeparatingLinearCoordinates.Constructions.SeparatingFiberCoordinates.exists_split L hLs v.val (hfinite (L v))
  have hpoly (j : Fin m) := GlobalEquation.Constructions.PeriodAlgebraicCoordinates.coordinate_equation Φ f hf hd L hker hs
    (SeparatingLinearCoordinates.Constructions.SeparatingFiberCoordinates.coordinate e j) (SeparatingLinearCoordinates.Constructions.SeparatingFiberCoordinates.coordinate_pair_surjective L e he j)
  choose k F hk hF hgen hroots using hpoly
  have hvi : v.val i = 1 := by rw [hv]; simp [ConeTangentF.Constructions.ConeTangent.parameterization]
  have hv0 : v.val ≠ 0 := by
    intro hzero
    have h := congrFun hzero i
    rw [hvi] at h
    exact one_ne_zero h
  have hLv : L v ≠ 0 := fun h => hv0 (hker v v.property h)
  have hfin : ((fun w : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) => L w) ⁻¹' {L v}).Finite := by
    apply Set.Finite.of_finite_image (f := (Subtype.val : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) → Fin (n + 1) → ℂ))
      ((hfinite (L v)).subset ?_) Subtype.val_injective.injOn
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩
  obtain ⟨q, hvq, hq, hdq⟩ := hInv
  refine ⟨L, m, e, F, he, ⟨q, hvq, hq, hdq⟩, ?_, ?_, ?_⟩
  · intro j hj
    exact (hF j 0).1.ne_zero (by rw [hj, Polynomial.map_zero])
  · intro j
    apply RegularCoordinate.Constructions.RegularCoordinateDerivative.derivative_ne_zero hp.isClosedMap
      ((SeparatingLinearCoordinates.Constructions.SeparatingFiberCoordinates.coordinate e j).continuous.comp continuous_subtype_val) q hq hvq hLv hfin
      (fun w hwL hwl => ?_) (F j) (hF j) (hgen j)
    · intro y t
      constructor
      · rintro ⟨w, hw⟩
        exact (hroots j y t).mp ⟨w, w.property, hw⟩
      · intro ht
        obtain ⟨w, hw, heq⟩ := (hroots j y t).mpr ht
        exact ⟨⟨w, hw⟩, heq⟩
    · apply Subtype.ext
      by_contra hwv
      exact hsep w w.property hwL hwv j hwl
  · intro j w hw
    exact (hroots j (L w) (SeparatingLinearCoordinates.Constructions.SeparatingFiberCoordinates.coordinate e j w)).mp ⟨w, hw, rfl⟩

end Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt.Constructions.RegularConeEquations

namespace Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt.Constructions.SplitPolynomialJacobian

/-! # RiemannProjectivity: the diagonal algebraic Jacobian of independent coordinate equations -/

open _root_.Polynomial

variable {n m : ℕ}

def equation (j : Fin m) (F : Polynomial (MvPolynomial (Fin n) ℂ)) :
    MvPolynomial (Fin n ⊕ Fin m) ℂ :=
  F.eval₂ (MvPolynomial.rename Sum.inl).toRingHom (MvPolynomial.X (Sum.inr j))

theorem eval_equation (j : Fin m) (F : Polynomial (MvPolynomial (Fin n) ℂ))
    (x : Fin n → ℂ) (z : Fin m → ℂ) :
    MvPolynomial.eval (Sum.elim x z) (equation j F) =
      F.eval₂ (MvPolynomial.eval x) (z j) := by
  induction F using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [equation, eval₂_add, map_add] at *; rw [hP, hQ]
  | monomial k a => simp [equation, MvPolynomial.eval_rename, Function.comp_def]

theorem pderiv_coefficient (t : Fin m) (p : MvPolynomial (Fin n) ℂ) :
    MvPolynomial.pderiv (Sum.inr t) (MvPolynomial.rename Sum.inl p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem pderiv_equation (j t : Fin m) (F : Polynomial (MvPolynomial (Fin n) ℂ)) :
    MvPolynomial.pderiv (Sum.inr t) (equation j F) =
      if j = t then equation j F.derivative else 0 := by
  classical
  induction F using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [equation, eval₂_add, map_add] at *
    rw [hP, hQ]
    split_ifs <;> simp
  | monomial k a =>
    simp only [equation, eval₂_monomial, derivative_monomial, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_pow]
    by_cases h : j = t
    · subst t
      simp [pderiv_coefficient, mul_assoc, mul_comm, mul_left_comm]
    · simp [h, pderiv_coefficient]

theorem jacobian_eq_diagonal (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ))
    (x : Fin n → ℂ) (z : Fin m → ℂ) :
    (fun j t => MvPolynomial.eval (Sum.elim x z)
      (MvPolynomial.pderiv (Sum.inr t) (equation j (F j)))) =
      Matrix.diagonal (fun j => ((F j).map (MvPolynomial.eval x)).derivative.eval (z j)) := by
  classical
  ext j t
  rw [pderiv_equation]
  by_cases h : j = t
  · subst t
    simp [eval_equation, derivative_map, eval_map]
  · simp [h]

theorem jacobian_det_ne_zero (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ))
    (x : Fin n → ℂ) (z : Fin m → ℂ)
    (h : ∀ j, ((F j).map (MvPolynomial.eval x)).derivative.eval (z j) ≠ 0) :
    Matrix.det (fun j t => MvPolynomial.eval (Sum.elim x z)
      (MvPolynomial.pderiv (Sum.inr t) (equation j (F j)))) ≠ 0 := by
  rw [jacobian_eq_diagonal, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => h j)

end Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt.Constructions.SplitPolynomialJacobian

namespace Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt.Constructions.JacobianLocalization

/-! # RiemannProjectivity: standard smoothness after inverting a presentation Jacobian -/

open _root_.Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {ι σ : Type*} [Finite ι] [Finite σ]

def presentation (P : PreSubmersivePresentation R S ι σ) :
    SubmersivePresentation R (Localization.Away P.jacobian) (Unit ⊕ ι) (Unit ⊕ σ) where
  __ := (PreSubmersivePresentation.localizationAway (Localization.Away P.jacobian)
    P.jacobian).comp P
  jacobian_isUnit := by
    rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
    exact (IsLocalization.Away.algebraMap_isUnit P.jacobian).mul
      (IsLocalization.Away.algebraMap_isUnit P.jacobian)

theorem isStandardSmooth (P : PreSubmersivePresentation R S ι σ) :
    Algebra.IsStandardSmooth R (Localization.Away P.jacobian) :=
  (presentation P).isStandardSmooth

end Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt.Constructions.JacobianLocalization

namespace Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt.Constructions.SmoothEquationPoint

/-! # RiemannProjectivity: genuine points of the smooth algebra cut out by the coordinate equations -/

open _root_.Polynomial _root_.MvPolynomial
open OAI.Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt.Constructions.SplitPolynomialJacobian

variable {n m : ℕ}

abbrev equationRing (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ)) :=
  MvPolynomial (Fin n ⊕ Fin m) ℂ ⧸ Ideal.span (Set.range (fun j => SplitPolynomialJacobian.equation j (F j)))

def presentation (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ)) :
    Algebra.PreSubmersivePresentation ℂ (equationRing F) (Fin n ⊕ Fin m) (Fin m) :=
  Algebra.PreSubmersivePresentation.naive Sum.inr Sum.inr_injective

def point (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ))
    (x : Fin n → ℂ) (z : Fin m → ℂ)
    (h : ∀ j, (F j).eval₂ (MvPolynomial.eval x) (z j) = 0) : equationRing F →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (Sum.elim x z)) (by
    change Ideal.span _ ≤ RingHom.ker (MvPolynomial.aeval (Sum.elim x z)).toRingHom
    apply Ideal.span_le.mpr
    rintro p ⟨j, rfl⟩
    change MvPolynomial.eval (Sum.elim x z) (SplitPolynomialJacobian.equation j (F j)) = 0
    rw [SplitPolynomialJacobian.eval_equation, h j])

theorem point_jacobian (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ))
    (x : Fin n → ℂ) (z : Fin m → ℂ)
    (h : ∀ j, (F j).eval₂ (MvPolynomial.eval x) (z j) = 0) :
    point F x z h (presentation F).jacobian =
      Matrix.det (fun j t => MvPolynomial.eval (Sum.elim x z)
        (MvPolynomial.pderiv (Sum.inr t) (SplitPolynomialJacobian.equation j (F j)))) := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  change MvPolynomial.eval (Sum.elim x z) (presentation F).jacobiMatrix.det = _
  rw [RingHom.map_det]
  rw [← Matrix.det_transpose]
  congr 1
  ext j t
  simp [presentation, Algebra.PreSubmersivePresentation.jacobiMatrix_naive]

theorem exists_smooth_point (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ))
    (x : Fin n → ℂ) (z : Fin m → ℂ)
    (hzero : ∀ j, (F j).eval₂ (MvPolynomial.eval x) (z j) = 0)
    (hderiv : ∀ j, ((F j).map (MvPolynomial.eval x)).derivative.eval (z j) ≠ 0) :
    Algebra.IsStandardSmooth ℂ (Localization.Away (presentation F).jacobian) ∧
    ∃ q : Localization.Away (presentation F).jacobian →ₐ[ℂ] ℂ,
      q.comp (Algebra.algHom ℂ (equationRing F) _) = point F x z hzero := by
  have hJ : point F x z hzero (presentation F).jacobian ≠ 0 := by
    rw [point_jacobian]
    exact SplitPolynomialJacobian.jacobian_det_ne_zero F x z hderiv
  exact ⟨JacobianLocalization.isStandardSmooth (presentation F),
    AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint (point F x z hzero) (presentation F).jacobian hJ,
    AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_comp _ _ _⟩

end Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt.Constructions.SmoothEquationPoint

namespace Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt.Constructions.AlgebraicLocalization

/-! # RiemannProjectivity: algebraicity survives localization of the coordinate algebra -/

variable {R A B : Type*} [CommRing R] [IsDomain R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

theorem isAlgebraic (M : Submonoid A) [IsLocalization M B] [Algebra.IsAlgebraic R A] :
    Algebra.IsAlgebraic R B := by
  constructor
  intro b
  obtain ⟨⟨a, m⟩, hab⟩ := IsLocalization.surj M b
  have ha : IsAlgebraic R (algebraMap A B a) :=
    (Algebra.IsAlgebraic.isAlgebraic (R := R) a).algebraMap
  have hm : IsAlgebraic R (algebraMap A B m.val) :=
    (Algebra.IsAlgebraic.isAlgebraic (R := R) m.val).algebraMap
  have hmul : IsAlgebraic R (algebraMap A B m.val * b) := by
    rw [mul_comm, hab]
    exact ha
  exact IsAlgebraic.of_mul (IsLocalization.map_units B m).mem_nonZeroDivisors hm hmul

end Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt.Constructions.AlgebraicLocalization

end

end OAI
