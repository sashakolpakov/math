import Mathlib
import OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType
import OAI.AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange
import OAI.AlgebraicGeometry.ComplexMultiplication.ThetaCompletion
import OAI.AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveHodgeQuotient
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveHodgeNaturality

/-! # Geometric Source -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

noncomputable section

/-!
# Concrete geometric source data for HeckeCycles

The source predicate below records a Hermitian lattice, rational symplectic
coordinates, the prescribed positive Lagrangian, its half-determinant frame,
an actual finite Schwartz input, and actual closed one-forms on projective
ball quotients. The classes are identified by the canonical integration map.
It contains no Hecke projector, slope, CM summand, or extraction assertion.

The Hermitian space is written in the diagonal coordinates (1,1,b) already
used by ArithmeticQuotient. A multiplicity line is E with Hermitian coefficient a. Frames
for its Lagrangian use L and the annihilator of L at the distinguished pair,
and the full selected embedding space at the other pairs. The period graph
is (Z x,x), matching the manuscript's convention. The squared half-determinant
is the determinant of the change from graph coordinates to these frames.
-/

open scoped Classical _root_.Manifold _root_.Matrix.Norms.Elementwise TensorProduct
open _root_.CategoryTheory
open OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField

abbrev Vec (K : Type*) := Fin 3 → K
abbrev BallChart := Fin 2 → ℂ

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [NumberField.IsCMField E]

def hermitian (b : E) (x y : Vec E) : E :=
  ∑ j, (if j = 2 then b else 1) * x j * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (y j)

/-- Raw lattice and signature data; these are not cohomological conditions. -/
structure BallDatum where
  b : E
  conjugate_b : ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E b = b
  negative : (b : ℂ).re < 0
  definite : ∀ τ : Gal(E/ℚ), τ ≠ 1 → τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E →
    0 < ((τ b : E) : ℂ).re
  other_place : ∃ τ : Gal(E/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E
  lattice : Submodule ℤ (Vec E)
  lattice_fg : lattice.FG
  lattice_full : Submodule.span ℚ (lattice : Set (Vec E)) = ⊤
  lattice_stable : ∀ (a : NumberField.RingOfIntegers E) (x : Vec E),
    x ∈ lattice → (a : E) • x ∈ lattice

namespace BallDatum

variable {E} (B : BallDatum E)

def domain : Set BallChart :=
  {z | Complex.normSq (z 0) + Complex.normSq (z 1) < -(B.b : ℂ).re}

theorem domain_isOpen : IsOpen B.domain := by
  apply isOpen_lt _ continuous_const
  exact (Complex.continuous_normSq.comp (continuous_apply 0)).add
    (Complex.continuous_normSq.comp (continuous_apply 1))

def domainOpen : TopologicalSpace.Opens BallChart := ⟨B.domain, B.domain_isOpen⟩
abbrev Domain := B.domainOpen

def lineVector (z : BallChart) : Vec ℂ := ![z 0, z 1, 1]

def principalLevel (N : ℕ) (g : Vec E ≃ₗ[E] Vec E) : Prop :=
  (∀ x y, hermitian E B.b (g x) (g y) = hermitian E B.b x y) ∧
  LinearMap.det g.toLinearMap = 1 ∧
  (∀ x, x ∈ B.lattice ↔ g x ∈ B.lattice) ∧
  ∀ x ∈ B.lattice, ∃ y ∈ B.lattice, g x - x = (N : ℤ) • y

def lineAction (g : Vec E ≃ₗ[E] Vec E) (z : BallChart) : BallChart :=
  let w := ((LinearMap.toMatrix' g.toLinearMap).map E.subtype).mulVec (lineVector z)
  fun j => w j.castSucc / w 2

/-- Actual projective quotient geometry, with the arithmetic fibers explicit. -/
def IsBallCover (N : ℕ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : B.Domain → X.analyticSpace) : Prop :=
  X.complexDimension = 2 ∧
  Function.Surjective π ∧ IsCoveringMap π ∧
  MDifferentiable 𝓘(ℂ, BallChart) 𝓘(ℂ, X.analyticModel) π ∧
  (∀ z, Function.Bijective
    (mfderiv 𝓘(ℂ, BallChart) 𝓘(ℂ, X.analyticModel) π z)) ∧
  ∀ z w, π z = π w ↔
    ∃ g : Vec E ≃ₗ[E] Vec E, B.principalLevel N g ∧ w.val = lineAction g z.val

end BallDatum

abbrev Ambient := Gal(E/ℚ) → Vec ℂ

def embeddingCoordinates (x : Vec E) : Ambient E :=
  fun τ j => ((τ (x j) : E) : ℂ)

def localPairing (b : E) (τ : Gal(E/ℚ)) (x y : Vec ℂ) : ℂ :=
  ∑ j, (if j = 2 then ((τ b : E) : ℂ) else 1) * x j * y j

/-- A representative of every conjugate pair, including the identity. -/
structure Places where
  count : ℕ
  representative : Fin count → Gal(E/ℚ)
  distinguished : Fin count
  identity : representative distinguished = 1
  complete : Function.Bijective
    (fun p : Fin count × Bool =>
      if p.2 then ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * representative p.1 else representative p.1)

abbrev Positions (places : Places E) := Fin places.count × Fin 3

def prescribed (B : BallDatum E) (places : Places E) (d : Gal(E/ℚ) → Bool)
    (z : BallChart) (w : Ambient E) : Prop :=
  ∀ i, if i = places.distinguished then
    w (places.representative i) ∈ ℂ ∙ BallDatum.lineVector z ∧
      localPairing E B.b (places.representative i) (BallDatum.lineVector z)
        (w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative i)) = 0
    else if d (places.representative i) then w (places.representative i) = 0
    else w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative i) = 0

/-- Coordinates in the explicit L, ann(L), and compact-place frames. -/
def adaptedCoordinates (places : Places E) (d : Gal(E/ℚ) → Bool) :
    Ambient E →ₗ[ℂ] (Positions E places → ℂ) where
  toFun w p := if p.1 = places.distinguished then
      if p.2 = 0 then w (places.representative p.1) 2
      else w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative p.1) (p.2 - 1)
    else if d (places.representative p.1) then
      w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative p.1) p.2
    else w (places.representative p.1) p.2
  map_add' _ _ := by ext p; simp only [Pi.add_apply]; split_ifs <;> rfl
  map_smul' _ _ := by ext p; simp only [Pi.smul_apply]; split_ifs <;> rfl

/-- Chosen rational symplectic coordinates and their actual complex extension. -/
structure SymplecticCoordinates (B : BallDatum E) (places : Places E) where
  a : E
  a_ne_zero : a ≠ 0
  a_real : ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E a = a
  delta : E
  delta_ne_zero : delta ≠ 0
  delta_imaginary : ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E delta = -delta
  rational : Vec E ≃ₗ[ℚ] ((Positions E places → ℚ) × (Positions E places → ℚ))
  complex : Ambient E ≃ₗ[ℂ] ((Positions E places → ℂ) × (Positions E places → ℂ))
  extends_rational : ∀ x,
    complex (embeddingCoordinates E x) =
      (fun j => ((rational x).1 j : ℂ), fun j => ((rational x).2 j : ℂ))
  symplectic : ∀ x y,
    Algebra.trace ℚ E (delta * a * hermitian E B.b x y) =
      ∑ j, ((rational x).1 j * (rational y).2 j -
        (rational y).1 j * (rational x).2 j)

def graphInAmbient {B : BallDatum E} {places : Places E}
    (C : SymplecticCoordinates E B places) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Positions E places)) :
    (Positions E places → ℂ) →ₗ[ℂ] Ambient E :=
  C.complex.symm.toLinearMap.comp
    ((Matrix.toLin' Z.matrix).prod LinearMap.id)

/-- The actual prescribed Lagrangian in rational Siegel coordinates. -/
structure LinePeriod (B : BallDatum E) (places : Places E) (d : Gal(E/ℚ) → Bool) where
  coordinates : SymplecticCoordinates E B places
  period : BallChart → ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Positions E places)
  holomorphic : DifferentiableOn ℂ (fun z => (period z).matrix) B.domain
  graph_prescribed : ∀ z ∈ B.domain, ∀ w : Ambient E,
    prescribed E B places d z w ↔
      (coordinates.complex w).1 = (period z).matrix.mulVec (coordinates.complex w).2
  halfDet : BallChart → ℂˣ
  halfDet_holomorphic : DifferentiableOn ℂ (fun z => (halfDet z : ℂ)) B.domain
  halfDet_square : ∀ z ∈ B.domain,
    (halfDet z : ℂ) ^ 2 = LinearMap.det
      ((adaptedCoordinates E places d).comp (graphInAmbient E coordinates (period z)))

abbrev FiniteAdeles := IsDedekindDomain.FiniteAdeleRing ℤ ℚ
abbrev FiniteInput (ι : Type*) :=
  {φ : (ι → FiniteAdeles) → ℂ // IsLocallyConstant φ ∧ HasCompactSupport φ}

def rationalPosition {ι : Type*} (x : ι → ℚ) : ι → FiniteAdeles :=
  fun j => algebraMap ℚ FiniteAdeles (x j)

/-- The source's actual theta series, before its quadratic completion. -/
def thetaSeries {ι : Type*} [Fintype ι]
    (φ : FiniteInput ι) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) : ℂ :=
  ∑' x : ι → ℚ, φ.val (rationalPosition x) * Complex.exp
    ((Real.pi : ℂ) * Complex.I *
      (∑ i, ∑ j, (x i : ℂ) * Z.matrix i j * (x j : ℂ)) +
      (2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (x i : ℂ) * z i)

/-- Order one is unchanged by completion. This is the literal projected
first derivative, including the half-determinant in the chosen frame. -/
def thetaOneForm {B : BallDatum E} {places : Places E} {d : Gal(E/ℚ) → Bool}
    (L : LinePeriod E B places d) (φ : FiniteInput (Positions E places))
    (z ξ : BallChart) : ℂ :=
  let derivative := fderiv ℂ (thetaSeries φ (L.period z)) 0
  let coefficients : Positions E places → ℂ := fun j => derivative (Pi.single j 1)
  let w := graphInAmbient E L.coordinates (L.period z) coefficients
  (L.halfDet z : ℂ) * localPairing E B.b 1 ![ξ 0, ξ 1, 0]
    (w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))

/-- A closed one-form whose pullback is the specified theta derivative. -/
def RepresentsTheta {B : BallDatum E} {places : Places E} {d : Gal(E/ℚ) → Bool}
    (L : LinePeriod E B places d) (φ : FiniteInput (Positions E places))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : B.Domain → X.analyticSpace)
    (ω : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0) : Prop :=
  ∀ (z : B.Domain) (ξ : BallChart),
    ω.val.val.val (π z)
      (fun _ : Fin 1 => mfderiv 𝓘(ℝ, BallChart) 𝓘(ℝ, X.analyticModel) π z ξ) =
        thetaOneForm E L φ z.val ξ

/-- The concrete source construction, independently of the extraction theorem. -/
def IsSourceBallThetaFamily
    (d : Gal(E/ℚ) → Bool) (Nbase : ℕ)
    (X : ℕ → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (Θ : ∀ N : ℕ, ComplexMultiplication.WeightOne.CM.Complexification ((X N).rationalCohomology 1)) : Prop :=
  ∃ (B : BallDatum E) (places : Places E) (L : LinePeriod E B places d)
    (φ : FiniteInput (Positions E places)),
    ∀ N : ℕ, 0 < N → Nbase ∣ N →
      ∃ (π : B.Domain → (X N).analyticSpace), B.IsBallCover N (X N) π ∧
        ∃ ω : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms
          (X N).analyticModel (X N).analyticSpace 1 0,
          RepresentsTheta E L φ (X N) π ω ∧
          ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace (X N).toOver) 1 (Θ N) =
            ((X N).deRhamBettiIso 1).hom ((X N).deRhamClass 1 ω.val)

/-- The geometric source construction supplies the original holomorphic type;
this is proved from the actual pure form and integration comparison. -/
theorem source_class_holomorphic
    (d : Gal(E/ℚ) → Bool) (Nbase : ℕ)
    (X : ℕ → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (Θ : ∀ N : ℕ, ComplexMultiplication.WeightOne.CM.Complexification ((X N).rationalCohomology 1))
    (hsource : IsSourceBallThetaFamily E d Nbase X Θ)
    (N : ℕ) (hN : 0 < N) (hdiv : Nbase ∣ N)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure ((X N).rationalCohomology 1))
    (hH : H.holomorphic = ((X N).pureBettiSubspace 1 0).comap
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace (X N).toOver) 1)) :
    Θ N ∈ H.holomorphic := by
  obtain ⟨B, places, L, φ, hlevels⟩ := hsource
  obtain ⟨π, _, ω, _, hclass⟩ := hlevels N hN hdiv
  rw [hH]
  change ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace (X N).toOver) 1 (Θ N) ∈
    (X N).pureBettiSubspace 1 0
  rw [hclass, ← (X N).clayHodgeToBetti_projection 1 0 ω,
    ← (X N).clayHodgeToBetti_range 1 0]
  exact LinearMap.mem_range_self _ _

omit [NumberField E] [NumberField.IsCMField E] in
/-- Coefficient extension respects the actual scheme pullback. -/
theorem complexification_pullback {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (n : ℕ)
    (x : ComplexMultiplication.WeightOne.CM.Complexification (Y.rationalCohomology n)) :
    ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) n
        ((Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) n f).hom.baseChange ℂ x) =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n f
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace Y.toOver) n x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z c =>
      simp only [LinearMap.baseChange_tmul, ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul]
      exact (congrArg (fun y : X.complexCohomology n => z • y)
        (ConcreteCategory.congr_hom (Betti.Scheme.schemeBettiRationalInclusion_naturality f n) c)).trans
          ((Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n f).hom.map_smul z _).symm
  | add x y hx hy => simp only [map_add, hx, hy]

omit [NumberField E] [NumberField.IsCMField E] in
/-- A matching restriction map is the actual rational scheme pullback;
its Hodge compatibility follows from pure-form naturality. -/
theorem actual_restriction_isHodgeMap {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver)
    (HX : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (X.rationalCohomology 1))
    (HY : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (Y.rationalCohomology 1))
    (hX : HX.holomorphic = (X.pureBettiSubspace 1 0).comap
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 1))
    (hY : HY.holomorphic = (Y.pureBettiSubspace 1 0).comap
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace Y.toOver) 1)) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap HY HX (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 f).hom := by
  intro x hx
  rw [hX]
  rw [hY] at hx
  change ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 1
    ((Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 f).hom.baseChange ℂ x) ∈ X.pureBettiSubspace 1 0
  rw [complexification_pullback]
  exact Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_mem_pureBettiSubspace f 1 0 hx

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
