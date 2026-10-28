import OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
import OAI.RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta

/-! # Data Theta -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.DataTheta

/-!
The complete AdelicTheta target uses actual rational theta sums and their completed
Taylor coefficients. The raw comparison data below carry no compatibility
axioms. Their arithmetic, geometric, and oscillator characterizations are
separate propositions to be asserted in the conclusion of AdelicTheta.
-/

open scoped _root_.NumberField Classical _root_.Matrix BigOperators BoundedContinuousFunction
open scoped _root_.Matrix.Norms.Elementwise
open _root_.Matrix

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallNatural.Factors
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation OAI.RepresentationTheory.Theta.Adelic.Evaluation
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

local instance (F : Type) [Field F] [NumberField F] (v : NumberField.InfinitePlace F) :
    MeasurableSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := borel _
local instance (F : Type) [Field F] [NumberField F] (v : NumberField.InfinitePlace F) :
    BorelSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := ⟨rfl⟩

variable (F : Type) [Field F] [NumberField F] {d : F} {m : ℕ}
variable (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (A : BallGeometryData.BallArithmeticData F d m H K)

/-- Raw coordinate choices and candidate comparison maps. No desired
identity is a field; the final theorem asserts all their characterizations. -/
structure ComparisonData where
  rationalPosition : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m) ≃ₗ[ℚ] (BallGeometryData.FrameIndex A → ℚ)
  realPosition : BallGeometryData.RealPositions A ≃L[ℝ] (BallGeometryData.FrameIndex A → ℝ)
  rationalPhase : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace F (3 * m) ≃ₗ[ℚ] ((BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℚ)
  realPhase : (Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) ≃L[ℝ]
    ((BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℝ)
  complexPhase : ((BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℂ) ≃L[ℂ] BallGeometryData.ComplexPhase A
  period : BallNatural.Ball → AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (BallGeometryData.FrameIndex A)
  frame : BallNatural.Ball → (Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ)ˣ
  halfFrame : BallNatural.Ball → ℂ
  ball : RationalSU.ArchimedeanSU F H →* BallNatural.BallGroup
  symplectic : RationalSU.ArchimedeanSU F H → AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks (BallGeometryData.FrameIndex A) ℝ
  rationalSymplectic : SpecialUnitary.SU H.val → AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks (BallGeometryData.FrameIndex A) ℚ
  gaussian : BallNatural.Ball → (BallGeometryData.FrameIndex A → ℂ) → ThetaEvaluation.ArchimedeanTests F (3 * m)

variable {F H K A}
variable (B : ComparisonData F H K A)

def swapPhase {I R : Type} (x : (I ⊕ I) → R) : (I ⊕ I) → R :=
  Sum.elim (fun i => x (.inr i)) (fun i => x (.inl i))

def blockMatrix {I R : Type} [Fintype I] [DecidableEq I] [CommRing R]
    (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks I R) : Matrix (I ⊕ I) (I ⊕ I) R :=
  Matrix.fromBlocks g.A g.B g.C g.D

def standardPairing {I R : Type} [Fintype I] [CommRing R]
    (x y : (I ⊕ I) → R) : R :=
  ∑ i, (x (.inl i) * y (.inr i) - x (.inr i) * y (.inl i))

/-- The entire Gaussian in rational Schrödinger coordinates. -/
def gaussianValue (Z : Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ)
    (z : BallGeometryData.FrameIndex A → ℂ) (x : BallGeometryData.FrameIndex A → ℝ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z x x +
    (2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (x i : ℂ) * z i)

def rationalWeight (f : FiniteSchwartz.finiteSchwartz F (3 * m)) (x : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) : ℂ :=
  Evaluation.finiteSchwartzFunction F (3 * m) f
    (fun i => algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (x i))

def thetaSummand (f : FiniteSchwartz.finiteSchwartz F (3 * m))
    (Z : Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ) (z : BallGeometryData.FrameIndex A → ℂ)
    (x : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) : ℂ :=
  rationalWeight f x * gaussianValue Z z (fun i => (B.rationalPosition x i : ℝ))

/-- The literal rational sum, weighted by the actual finite Schwartz
function. Its convergence is part of the complete conclusion. -/
def rationalTheta (f : FiniteSchwartz.finiteSchwartz F (3 * m))
    (Z : Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ) (z : BallGeometryData.FrameIndex A → ℂ) : ℂ :=
  ∑' x : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m), thetaSummand B f Z z x

def completedTheta (f : FiniteSchwartz.finiteSchwartz F (3 * m))
    (Z : Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ) (z : BallGeometryData.FrameIndex A → ℂ) : ℂ :=
  AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor (((Real.pi : ℂ) / 2) •
    AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear ((AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z)⁻¹)) z * rationalTheta B f Z z

abbrev TaylorTensor (a : ℕ) :=
  ContinuousMultilinearMap ℂ (fun _ : Fin a => BallGeometryData.FrameIndex A → ℂ) ℂ

def completedTensor (f : FiniteSchwartz.finiteSchwartz F (3 * m)) (a : ℕ)
    (Z : Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ) : TaylorTensor (A := A) a :=
  ((Nat.factorial a : ℂ)⁻¹) • iteratedFDeriv ℂ a (completedTheta B f Z) 0

/-- The same completed tensor expressed in the natural Hodge frame and
the natural square-root line. The change of frame is characterized
geometrically in `GeometryIdentification`, not selected by a theta law. -/
def geometricTensor (f : FiniteSchwartz.finiteSchwartz F (3 * m)) (a : ℕ) (z : BallNatural.Ball) :
    TaylorTensor (A := A) a :=
  (B.halfFrame z)⁻¹ • (completedTensor B f a (B.period z).matrix).compContinuousLinearMap
    (fun _ => (Matrix.toLin' (B.frame z).invᵀ).toContinuousLinearMap)

variable (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

/-- All changes of rational and real coordinates are tied to the actual
trace tensor space and to AdelicSplitting's given rational/local polarizations. -/
def CoordinateIdentification : Prop :=
  (∀ x i, B.realPosition (BallGeometryData.archPositions A x) i = (B.rationalPosition x i : ℝ)) ∧
  (∀ x i, B.rationalPhase x (.inl i) =
      B.rationalPosition (fun j => x (.inl j)) i) ∧
  (∀ x y, standardPairing (B.rationalPhase x) (B.rationalPhase y) =
      Algebra.trace ℚ F (Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing 3 m x y)) ∧
  (∀ x i, B.realPhase
      (fun v j => A.real v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) (x j))) i =
        (B.rationalPhase x i : ℝ)) ∧
  (∀ x i, B.realPhase x (.inl i) =
      B.realPosition (fun v j => x v (.inl j)) i) ∧
  (∀ x y, standardPairing (B.realPhase x) (B.realPhase y) =
      ∑ v, standardPairing (x v) (y v)) ∧
  (∀ s, B.complexPhase (fun i =>
      (B.realPhase (fun v j => A.real v
        ((P.localFrame (.inl (A.enumerate v))).coordinates (s v) j)) i : ℂ)) =
      BallGeometryData.realTensorComponents A s) ∧
  (∀ g x, (blockMatrix (B.symplectic g)).mulVec (swapPhase (B.realPhase x)) =
      swapPhase (B.realPhase (fun v i => A.real v
        (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.AdelicSplitting.Assembly.Construction.localDualAction F d 3 m H K P (.inl (A.enumerate v))
          (FiniteSchwartz.localSUToPair F H K (.inl (A.enumerate v)) (g (A.enumerate v))))
            (fun j => (A.real v).symm (x v j)) i)))) ∧
  (∀ g x, (blockMatrix (B.rationalSymplectic g)).mulVec (swapPhase (B.rationalPhase x)) =
      swapPhase (B.rationalPhase
        (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational
          (SpecialUnitary.includeUnitary H.val g, 1)) x))) ∧
  (∀ g, blockMatrix (B.symplectic (RationalSU.rationalArchimedeanSU F H g)) =
      (blockMatrix (B.rationalSymplectic g)).map (algebraMap ℚ ℝ))

/-- The period map, Hodge frame, and half-determinant frame are identified
with explicit geometric objects. No oscillator or theta equality is a
hypothesis of this proposition. -/
def GeometryIdentification : Prop :=
  Continuous B.ball ∧
  (∀ g, (BallNatural.asSL (B.ball g)).val = BallGeometryData.standardMatrix A g A.distinguished) ∧
  BallGeometryData.BallHolomorphic (fun z => (B.period z).matrix) ∧
  BallGeometryData.BallHolomorphic (fun z => (B.frame z).val) ∧
  BallGeometryData.BallHolomorphic B.halfFrame ∧
  (∀ z, B.halfFrame z ≠ 0 ∧ B.halfFrame z ^ 2 = (B.frame z).val.det) ∧
  (∀ z a, B.complexPhase
      (Sum.elim ((B.frame z).val.mulVec a)
        ((B.period z).matrix.mulVec ((B.frame z).val.mulVec a))) = BallGeometryData.geometricFrame A z a) ∧
  (∀ z w, w ∈ BallGeometryData.HodgeSubspace A z ↔ ∃ t : BallGeometryData.FrameIndex A → ℂ,
      B.complexPhase (Sum.elim t ((B.period z).matrix.mulVec t)) = w) ∧
  (∀ g z a, BallGeometryData.geometricAction A g (BallGeometryData.geometricFrame A z a) =
      BallGeometryData.geometricFrame A (B.ball g • z) ((BallGeometryData.frameMatrix A g z).mulVec a)) ∧
  (∀ g z, (BallGeometryData.frameMatrix A g z).det =
      DeterminantCoordinates.hodgeDeterminantFactor
        (BallNatural.asSL (B.ball g)) z.val ^ m) ∧
  (∀ g z, B.period (B.ball g • z) = (B.symplectic g).transformSiegel (B.period z)) ∧
  (∀ g z, (B.symplectic g).complexify.denominator (B.period z).matrix * (B.frame z).val =
      (B.frame (B.ball g • z)).val * BallGeometryData.frameMatrix A g z)

variable (hd : d ≠ 0) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
variable (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C P)

/-- Evaluation of the ACTUAL oscillator transform of the standard
Gaussian at zero determines the determinant branch. It is not defined
using the requested geometric transformation identity. -/
def oscillatorFactor (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball) : ℂ :=
  (∏ v : Fin A.places,
    ((SpecialUnitaryTheta.archimedeanAction F H K hd C P D g (B.gaussian z 0)) (A.enumerate v)).val 0)⁻¹

def archTestValue (φ : ThetaEvaluation.ArchimedeanTests F (3 * m)) (x : BallGeometryData.RealPositions A) : ℂ :=
  ∏ v : Fin A.places, (φ (A.enumerate v)).val (fun i => (A.real v).symm (x v i))

/-- Gaussian comparison, double-cover membership, and the geometric
half-determinant identification are all conclusions. The last equality
is literally the previously constructed natural line action. -/
def OscillatorIdentification : Prop :=
  (∀ z ξ x, archTestValue (A := A) (B.gaussian z ξ) x =
      gaussianValue (B.period z).matrix ξ (B.realPosition x)) ∧
  (∀ v g, FiniteSchwartz.localSUSplitting F H K hd C P D (.inl v) g ∈
      Weil.Local.FunctionsMetaplectic.Construction.metaplecticSubgroup (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) (3 * m)
        (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inl v))) ∧
  (∀ g z, oscillatorFactor B P hd C D g z ≠ 0 ∧
      oscillatorFactor B P hd C D g z ^ 2 =
        ((B.symplectic g).complexify.denominator (B.period z).matrix).det) ∧
  (∀ g, BallGeometryData.BallHolomorphic (oscillatorFactor B P hd C D g)) ∧
  Continuous (fun p : RationalSU.ArchimedeanSU F H × BallNatural.Ball => oscillatorFactor B P hd C D p.1 p.2) ∧
  (∀ g h z, oscillatorFactor B P hd C D (g * h) z =
      oscillatorFactor B P hd C D g (B.ball h • z) * oscillatorFactor B P hd C D h z) ∧
  (∀ z, oscillatorFactor B P hd C D 1 z = 1) ∧
  (∀ g z ξ x,
      archTestValue (A := A) (SpecialUnitaryTheta.archimedeanAction F H K hd C P D g (B.gaussian z ξ)) x =
        (oscillatorFactor B P hd C D g z)⁻¹ *
          Complex.exp (-(B.symplectic g).thetaCorrectionForm (B.period z) ξ ξ) *
          gaussianValue (B.period (B.ball g • z)).matrix
            ((B.symplectic g).jacobiChange (B.period z) ξ) (B.realPosition x)) ∧
  (∀ g z a, (oscillatorFactor B P hd C D g z * B.halfFrame z /
        B.halfFrame (B.ball g • z)) * a =
      (BallNatural.LineLift.naturalLineLift m (B.ball g) (z, a)).2) ∧
  (∀ χ : BallNatural.BallGroup →ₜ* Circle, ∀ g, χ g = 1)

end RepresentationTheory.Theta.Adelic.DataTheta

namespace RepresentationTheory.Theta.Adelic.DataTheta.Descent

/-! Completed theta covariance and descent on actual principal congruence
orbit spaces. All predicates here are conclusions of the new statement. -/

open scoped _root_.NumberField Classical _root_.Matrix BigOperators BoundedContinuousFunction
open scoped _root_.Matrix.Norms.Elementwise
open _root_.Matrix

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallNatural.Factors
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : BallGeometryData.BallArithmeticData F d m H K}
variable (B : ComparisonData F H K A)
variable (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)
variable (hd : d ≠ 0) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
variable (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C P)

/-- The additive-character convention for the positive Siegel model.
This is an explicit scalar normalization, with no assertion about Weil
operators, rational compatibility, or theta covariance. The general
splitting clause also covers every other global additive character. -/
def StandardArchCharacter (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) : Prop :=
  ∀ v : Fin A.places, ∀ t : ℝ,
    Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inl (A.enumerate v)) ((A.real v).symm t) =
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ))

/-- A support lattice and its weight identify the rational sum with the
actual CompletedTheta completed construction, including its Taylor derivatives. -/
def LatticeIdentification : Prop :=
  ∀ f : FiniteSchwartz.finiteSchwartz F (3 * m),
    ∃ L : Submodule ℤ (BallGeometryData.FrameIndex A → ℝ), DiscreteTopology L ∧
      ∃ φ : L →ᵇ ℂ,
        (∀ l : L, ∃ x : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m),
          (fun i => (B.rationalPosition x i : ℝ)) = l.val) ∧
        (∀ x, (fun i => (B.rationalPosition x i : ℝ)) ∉ L → rationalWeight f x = 0) ∧
        (∀ x hx, φ ⟨fun i => (B.rationalPosition x i : ℝ), hx⟩ = rationalWeight f x) ∧
        (∀ (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (BallGeometryData.FrameIndex A)) ξ,
          rationalTheta B f Z.matrix ξ = Definitions.theta L φ Z.matrix ξ ∧
          completedTheta B f Z.matrix ξ = Definitions.completedTheta L φ Z.matrix ξ) ∧
        (∀ a (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (BallGeometryData.FrameIndex A)),
          completedTensor B f a Z.matrix = Definitions.completedTensor L φ a Z.matrix)

/-- Analytic regularity and exact comparison with the independently
constructed adelic theta functional. -/
def ThetaConstruction : Prop :=
  LatticeIdentification B ∧
  (∀ f (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (BallGeometryData.FrameIndex A)) ξ,
    Summable (thetaSummand B f Z.matrix ξ)) ∧
  (∀ f z ξ, rationalTheta B f (B.period z).matrix ξ =
      ThetaEvaluation.theta F (3 * m) (B.gaussian z ξ) f) ∧
  (∀ f a, ContDiffOn ℝ ⊤ (completedTensor B f a) Definitions.siegelDomain) ∧
  (∀ f a (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (BallGeometryData.FrameIndex A)) (σ : Equiv.Perm (Fin a)) v,
      completedTensor B f a Z.matrix (fun i => v (σ i)) = completedTensor B f a Z.matrix v) ∧
  (∀ f a, BallGeometryData.BallSmooth (geometricTensor B f a))

/-- Rational SU Hecke covariance of the actual completed theta function
and all Taylor tensors. The last equality is in the natural geometric
half-determinant and Hodge frames, rather than an arbitrary scalar model. -/
def RationalHeckeCovariance : Prop :=
  ∀ (g : SpecialUnitary.SU H.val) (f : FiniteSchwartz.finiteSchwartz F (3 * m)),
    let gArch := RationalSU.rationalArchimedeanSU F H g
    let fnew := FiniteSchwartz.finiteAction F H K hd C P D (RationalSU.rationalFiniteSU F H g) f
    (∀ z ξ,
      rationalTheta B fnew (B.period (B.ball gArch • z)).matrix
          ((B.symplectic gArch).jacobiChange (B.period z) ξ) =
        oscillatorFactor B P hd C D gArch z *
          (Complex.exp ((B.symplectic gArch).thetaCorrectionForm (B.period z) ξ ξ) *
            rationalTheta B f (B.period z).matrix ξ)) ∧
    (∀ z ξ,
      completedTheta B fnew (B.period (B.ball gArch • z)).matrix
          ((B.symplectic gArch).jacobiChange (B.period z) ξ) =
        oscillatorFactor B P hd C D gArch z * completedTheta B f (B.period z).matrix ξ) ∧
    (∀ a z v,
      completedTensor B fnew a (B.period (B.ball gArch • z)).matrix
          (fun i => (B.symplectic gArch).jacobiChange (B.period z) (v i)) =
        oscillatorFactor B P hd C D gArch z * completedTensor B f a (B.period z).matrix v) ∧
    (∀ a z v,
      geometricTensor B fnew a (B.ball gArch • z)
          (fun i => BallGeometryData.dualFrameChange A gArch z (v i)) =
        BallNatural.Factors.naturalHalfFactor m (B.ball gArch) z * geometricTensor B f a z v)

/-- Orbit relation of the actual rational principal congruence group on
negative lines, in the standard ball chart. -/
def BallOrbit (N : ℕ) (z w : BallNatural.Ball) : Prop :=
  ∃ g : SpecialUnitary.SU H.val, BallGeometryData.PrincipalLevel N g ∧ B.ball (RationalSU.rationalArchimedeanSU F H g) • z = w

/-- The symmetric tensors, not the larger full tensor power. -/
abbrev SymmetricTensor (a : ℕ) :=
  {T : TaylorTensor (A := A) a //
    ∀ (σ : Equiv.Perm (Fin a)) v, T (fun i => v (σ i)) = T v}

/-- Orbit relation on the actual half-determinant times symmetric Hodge
tensor bundle, written as symmetric multilinear forms on dual variables. -/
def TensorOrbit (N a : ℕ)
    (p q : BallNatural.Ball × SymmetricTensor (A := A) a) : Prop :=
  ∃ g : SpecialUnitary.SU H.val, BallGeometryData.PrincipalLevel N g ∧
    B.ball (RationalSU.rationalArchimedeanSU F H g) • p.1 = q.1 ∧
    ∀ v, q.2.val (fun i => BallGeometryData.dualFrameChange A (RationalSU.rationalArchimedeanSU F H g) p.1 (v i)) =
      BallNatural.Factors.naturalHalfFactor m (B.ball (RationalSU.rationalArchimedeanSU F H g)) p.1 * p.2.val v

/-- Cofinal compact open levels contain genuine principal congruence
groups and fix every prescribed finite family of inputs. The completed
tensors descend to sections of the explicit tensor-bundle orbit spaces.
There is no assumption that an arbitrary finite-index kernel is congruence. -/
def CongruenceDescent : Prop :=
  ∀ (Φ : Finset (FiniteSchwartz.finiteSchwartz F (3 * m))) (K₀ : OpenSubgroup (FiniteSchwartz.FiniteSU F H))
    (N₀ : ℕ), 0 < N₀ →
    ∃ N : ℕ, 0 < N ∧ N₀ ∣ N ∧
      (∀ g : SpecialUnitary.SU H.val, BallGeometryData.PrincipalLevel N g →
        ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) ∧
      ∃ L : OpenSubgroup (FiniteSchwartz.FiniteSU F H), IsCompact (L : Set (FiniteSchwartz.FiniteSU F H)) ∧ L ≤ K₀ ∧
        (∀ g : SpecialUnitary.SU H.val, BallGeometryData.PrincipalLevel N g → RationalSU.rationalFiniteSU F H g ∈ L) ∧
        (∀ f ∈ Φ, ∀ g ∈ L, FiniteSchwartz.finiteAction F H K hd C P D g f = f) ∧
        ∃ R : Setoid BallNatural.Ball, (∀ z w, R.r z w ↔ BallOrbit B N z w) ∧
          CompactSpace (Quotient R) ∧ T2Space (Quotient R) ∧
          SecondCountableTopology (Quotient R) ∧
          ∀ a : ℕ, ∃ S : Setoid (BallNatural.Ball × SymmetricTensor (A := A) a),
            (∀ p q, S.r p q ↔ TensorOrbit B N a p q) ∧
            ∃ projection : Quotient S → Quotient R,
              Continuous projection ∧
              (∀ p, projection (Quotient.mk S p) = Quotient.mk R p.1) ∧
              ∀ f ∈ Φ, ∃ T : BallNatural.Ball → SymmetricTensor (A := A) a,
                (∀ z, (T z).val = geometricTensor B f a z) ∧
                ∃ descended : Quotient R → Quotient S,
                Continuous descended ∧
                (∀ q, projection (descended q) = q) ∧
                ∀ z, descended (Quotient.mk R z) =
                  Quotient.mk S (z, T z)

end RepresentationTheory.Theta.Adelic.DataTheta.Descent

namespace RepresentationTheory.Theta.Adelic.DataTheta.SymmetricGeometricTensor

/-! The smooth geometric theta tensors take values in the symmetric
subspace, with its actual subspace topology. -/

open scoped Classical _root_.NumberField _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

theorem ballSmooth_continuous {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : BallNatural.Ball → V) (h : BallGeometryData.BallSmooth f) : Continuous f := by
  have hc := h.continuousOn.domRestrict
  apply hc.congr
  intro z
  exact dite_eq_left z.property

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : BallGeometryData.BallArithmeticData F d m H K}
variable (B : ComparisonData F H K A) (h : Descent.ThetaConstruction B)

include h in
theorem geometricTensor_symmetric (f : FiniteSchwartz.finiteSchwartz F (3 * m)) (a : ℕ)
    (z : BallNatural.Ball) (σ : Equiv.Perm (Fin a)) (v : Fin a → BallGeometryData.FrameIndex A → ℂ) :
    geometricTensor B f a z (fun i => v (σ i)) = geometricTensor B f a z v := by
  change (B.halfFrame z)⁻¹ * completedTensor B f a (B.period z).matrix
      (fun i => (B.frame z).invᵀ.mulVec (v (σ i))) =
    (B.halfFrame z)⁻¹ * completedTensor B f a (B.period z).matrix
      (fun i => (B.frame z).invᵀ.mulVec (v i))
  exact congrArg ((B.halfFrame z)⁻¹ * ·)
    (h.2.2.2.2.1 f a (B.period z) σ (fun i => (B.frame z).invᵀ.mulVec (v i)))

def symmetricGeometricTensor (f : FiniteSchwartz.finiteSchwartz F (3 * m)) (a : ℕ)
    (z : BallNatural.Ball) : Descent.SymmetricTensor (A := A) a :=
  ⟨geometricTensor B f a z, geometricTensor_symmetric B h f a z⟩

theorem symmetricGeometricTensor_continuous (f : FiniteSchwartz.finiteSchwartz F (3 * m)) (a : ℕ) :
    Continuous (symmetricGeometricTensor B h f a) :=
  (ballSmooth_continuous _ (h.2.2.2.2.2 f a)).subtype_mk _

end RepresentationTheory.Theta.Adelic.DataTheta.SymmetricGeometricTensor

end

end OAI
