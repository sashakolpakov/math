import Mathlib
import OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType
import OAI.AlgebraicGeometry.ComplexMultiplication.WeightedTheta
import OAI.AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion
import OAI.RepresentationTheory.Weil.Local.Generators
import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-! # Prerequisites -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core

noncomputable section

/-!
# Explicit prerequisite propositions for RadialDilation

These are proposition-valued definitions, not applications of statement stubs.
They mirror the six supplied specifications. The reserved binder `Σ` is renamed
`reps`; the finite-dimensional matrix operator norm is selected for CompletedTheta;
unused proof binders are prefixed with `_`; ambient namespaces are explicit.
LocalWeil and PoissonAutomorphy use the repaired concrete constructions, imported without their
unproved target declarations. Their full target propositions remain hypotheses.
No generator, automorphy, or target conclusion is asserted by these definitions.
-/

open scoped Classical
open OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField

/- LefschetzNormalization: proposition and definitions mirrored from Statements/LefschetzNormalization.lean. -/
namespace LefschetzNormalization
open scoped TensorProduct

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]

abbrev G := Gal(E/ℚ)

abbrev Sign := AlgebraicGeometry.ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
  (fun τ : G E => AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)

abbrev FourTypes := Fin 4 → Sign E

def switchLabels : Fin 4 → G E :=
  fun i => if i.val < 2 then 1 else AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E

def embeddingGenerator (τ : G E) : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification E :=
  AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ)

def Proposition : Prop := ∀
    (s : ℕ)
    (_hdegree : Fintype.card (G E) = 2 * s)
    (A₂ : Sign E → Sign E → G E → G E → Prop)
    (A₄ : FourTypes E → (Fin 4 → G E) → Prop)
    (_h11 :
      ∀ (u v : Sign E) (a b : G E),
        (∀ σ : G E,
          AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (u.val (σ * a)) +
            AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val (σ * b)) = 0) →
        A₂ u v a b)
    (_hproduct :
      ∀ (v : FourTypes E) (a : Fin 4 → G E)
        (p : Equiv.Perm (Fin 4)),
        A₂ (v (p 0)) (v (p 1)) (a (p 0)) (a (p 1)) →
        A₂ (v (p 2)) (v (p 3)) (a (p 2)) (a (p 3)) →
        A₄ v a)
    (_hscalar :
      ∀ (v : FourTypes E) (a : Fin 4 → G E) (g : G E),
        A₄ v (fun i => g * a i) ↔ A₄ v a)
    (_htransfer :
      ∀ (u v : FourTypes E) (a b : Fin 4 → G E)
        (f : Fin 4 → (E →ₗ[ℚ] E)),
        (∀ i,
          AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (u i))
            (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)) (f i)) →
        (∀ i,
          (f i).baseChange ℂ (embeddingGenerator E (a i)) =
            embeddingGenerator E (b i)) →
        A₄ u a → A₄ v b)
    (v : FourTypes E)
    (_hbalance :
      ∀ τ : G E,
        AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val τ) + AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val τ) =
          AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val τ) + AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val τ)),

    ((¬ ∃ g : G E,
        (v 0).val g = true ∧ (v 1).val g = true) ∧
      (∀ τ : G E,
        (v 1).val τ = !((v 0).val τ) ∧
        (v 3).val τ = !((v 2).val τ)) ∧
      A₄ v (switchLabels E))
    ∨

    (∃ (g : G E) (w : FourTypes E)
        (d : Fin 4 → G E → Bool) (reps : Finset (G E)),
      (∀ i σ, (w i).val σ = (v i).val (σ * g)) ∧
      (∀ i, (w i).val 1 = true) ∧
      (∀ τ : G E,
        AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue ((w 0).val τ) + AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue ((w 1).val τ) =
          AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue ((w 2).val τ) + AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue ((w 3).val τ)) ∧

      (∀ i,
        AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (w i))
          (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)) (g⁻¹).toLinearMap) ∧
      (∀ τ : G E,
        (g⁻¹).toLinearMap.baseChange ℂ (embeddingGenerator E τ) =
          embeddingGenerator E (τ * g)) ∧
      (∀ i τ, d i τ = (w i).val τ⁻¹) ∧
      (∀ i τ, d i (AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) = !(d i τ)) ∧
      (1 : G E) ∈ reps ∧
      (∀ τ : G E,
        τ ∈ reps ↔ AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ ∉ reps) ∧
      reps.card = s ∧
      (A₄ w (switchLabels E) ↔ A₄ v (switchLabels E)) ∧
      ((s = 1 ∧ A₄ v (switchLabels E)) ∨ 2 ≤ s))

end LefschetzNormalization

/- CotangentBundle: proposition and definitions mirrored from Statements/CotangentBundle.lean. -/
namespace CotangentBundle
universe u v

structure BundleCalculus
    (B : Type u) (A : Type v)
    [CommSemiring B] [CommGroup A] where
  line : A →* B
  rank : B →+* ℕ
  dual : B →+* B
  det : B → A
  shortExact : B → B → B → Prop

  rank_line : ∀ a, rank (line a) = 1
  rank_dual : ∀ X, rank (dual X) = rank X
  dual_involutive : ∀ X, dual (dual X) = X

  det_line : ∀ a, det (line a) = a
  det_sum : ∀ X Y, det (X + Y) = det X * det Y
  det_tensor : ∀ X Y,
    det (X * Y) = det X ^ rank Y * det Y ^ rank X
  det_dual : ∀ X, det (dual X) = (det X)⁻¹

  rank_exact : ∀ X Y Z, shortExact X Y Z →
    rank Y = rank X + rank Z
  det_exact : ∀ X Y Z, shortExact X Y Z →
    det Y = det X * det Z

variable {B : Type u} {A : Type v}
  [CommSemiring B] [CommGroup A]

def projectiveCotangent
    (C : BundleCalculus B A) (L : A) (Q : B) : B :=
  C.dual (C.dual (C.line L) * Q)

def Proposition : Prop := ∀
    (C : BundleCalculus B A)
    (n : ℕ) (L : A) (Vμ Q P K ℱ : B)
    (_h_rankV : C.rank Vμ = 3)
    (_h_rankP : C.rank P = n)
    (_h_quotient : C.shortExact (C.line L) Vμ Q)
    (_h_specialUnitary : C.det Vμ = 1)
    (_h_multiplicity : C.det P = 1)
    (_h_compactPlaces : C.det K = 1)
    (_h_L3_2 :
      ℱ = C.line L * P + C.dual Q * C.dual P + K),
    C.det ℱ = L ^ (2 * n) ∧
    (∃ H : A, H = L ^ n ∧ H ^ 2 = C.det ℱ) ∧
    projectiveCotangent C L Q = C.line L * C.dual Q

end CotangentBundle

/- CompletedTheta: proposition and definitions mirrored from Statements/CompletedTheta.lean. -/
section
open scoped _root_.Matrix BoundedContinuousFunction _root_.Matrix.Norms.Operator
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def Theta.theta
    (L : Submodule ℤ (ι → ℝ)) (φ : L →ᵇ ℂ)
    (Z : Matrix ι ι ℂ) (z : ι → ℂ) : ℂ :=
  ∑' x : L,
    φ x * Complex.exp
      ((Real.pi : ℂ) * Complex.I *
          AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z (x : ι → ℝ) (x : ι → ℝ) +
        (2 * (Real.pi : ℂ) * Complex.I) *
          (∑ i, (((x : ι → ℝ) i : ℝ) : ℂ) * z i))

def Theta.completedTheta
    (L : Submodule ℤ (ι → ℝ)) (φ : L →ᵇ ℂ)
    (Z : Matrix ι ι ℂ) (z : ι → ℂ) : ℂ :=
  AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor
      (((Real.pi : ℂ) / 2) •
        AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear ((AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z)⁻¹)) z *
    Theta.theta L φ Z z

def Theta.completedTensor
    (L : Submodule ℤ (ι → ℝ)) (φ : L →ᵇ ℂ)
    (a : ℕ) (Z : Matrix ι ι ℂ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin a => ι → ℂ) ℂ :=
  ((Nat.factorial a : ℂ)⁻¹) •
    iteratedFDeriv ℂ a (Theta.completedTheta L φ Z) 0

def Theta.siegelDomain : Set (Matrix ι ι ℂ) :=
  {Z | Z.IsSymm ∧ Matrix.PosDef (fun i j => (Z i j).im)}

def Theta.Proposition : Prop := ∀
    (L Lnew : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [DiscreteTopology Lnew]
    (φ : L →ᵇ ℂ) (φnew : Lnew →ᵇ ℂ)
    (gQ : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℚ)
    (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ)
    (_hA : g.A = gQ.A.map (algebraMap ℚ ℝ))
    (_hB : g.B = gQ.B.map (algebraMap ℚ ℝ))
    (_hC : g.C = gQ.C.map (algebraMap ℚ ℝ))
    (_hD : g.D = gQ.D.map (algebraMap ℚ ℝ))
    (halfDet : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι → ℂ)
    (_hHalfDet : ∀ Z,
      halfDet Z ^ 2 = (g.complexify.denominator Z.matrix).det)
    (_hPoisson : ∀ (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ),
      Theta.theta Lnew φnew (g.transformSiegel Z).matrix
          (g.jacobiChange Z z) =
        halfDet Z *
          (Complex.exp (g.thetaCorrectionForm Z z z) *
            Theta.theta L φ Z.matrix z)),

    (∀ a : ℕ,
      ContDiffOn ℝ ⊤ (Theta.completedTensor L φ a) Theta.siegelDomain) ∧

    (∀ (a : ℕ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι)
        (σ : Equiv.Perm (Fin a)) (v : Fin a → (ι → ℂ)),
      Theta.completedTensor L φ a Z.matrix (fun i => v (σ i)) =
        Theta.completedTensor L φ a Z.matrix v) ∧

    (∀ (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ),
      Theta.completedTheta Lnew φnew (g.transformSiegel Z).matrix
          (g.jacobiChange Z z) =
        halfDet Z * Theta.completedTheta L φ Z.matrix z) ∧

    (∀ (a : ℕ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι)
        (v : Fin a → (ι → ℂ)),
      Theta.completedTensor Lnew φnew a (g.transformSiegel Z).matrix
          (fun i => g.jacobiChange Z (v i)) =
        halfDet Z * Theta.completedTensor L φ a Z.matrix v)

end

/- NormOneApproximation: proposition and definitions mirrored from Statements/NormOneApproximation.lean. -/
namespace NormOneApproximation
open _root_.NumberField IsDedekindDomain

def Proposition : Prop := ∀
    {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [IsGalois ℚ E]
    (w wbar : HeightOneSpectrum (𝓞 E))
    (_hconj : wbar.asIdeal =
      Ideal.map
        (NumberField.IsCMField.ringOfIntegersComplexConj E).toRingHom
        w.asIdeal)
    (_hsplit : w ≠ wbar),
    ∃ (r : Eˣ) (M : ℕ),
      0 < M ∧
      (r : E) * NumberField.IsCMField.complexConj E (r : E) = 1 ∧
      w.valuation E (r : E) = WithZero.exp (-(M : ℤ)) ∧
      wbar.valuation E (r : E) = WithZero.exp (M : ℤ) ∧
      (∀ p : HeightOneSpectrum (𝓞 E),
        p ≠ w → p ≠ wbar → p.valuation E (r : E) = 1) ∧
      (∀ (S : Finset (HeightOneSpectrum (𝓞 E)))
          (depth : HeightOneSpectrum (𝓞 E) → ℕ),
        w ∉ S → wbar ∉ S →
        ∃ N : ℕ, 0 < N ∧
          ∀ p ∈ S,
            p.valuation E ((r : E) ^ N - 1) ≤
              WithZero.exp (-(depth p : ℤ)))

end NormOneApproximation

/- LocalWeil: repaired proposition mirrored from Statements/LocalWeil.lean. -/
namespace LocalWeil

open OAI.RepresentationTheory.Weil.Local.Generators.Construction _root_.MeasureTheory Filter
open scoped BigOperators _root_.Topology

def Proposition : Prop := ∀
    (k : Type) [NormedField k] [CompleteSpace k]
    [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (_hNondiscrete : ¬ DiscreteTopology k)
    (n : ℕ) (_hn : 0 < n)
    (ψ : AddChar k ℂ)
    (_hContinuous : Continuous (fun t : k => ψ t))
    (_hUnitary : ∀ t : k, ‖ψ t‖ = 1)
    (_hNontrivial : ∃ t : k, ψ t ≠ 1),

    (0 < Weil.Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ) ∧
    (Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure ∧

    (∀ a : k, a ≠ 0 →
      Tendsto (Weil.Local.FunctionsMetaplectic.Construction.regularizedGaussian k ψ a) (𝓝[>] (0 : ℝ))
        (𝓝 (Weil.Local.FunctionsMetaplectic.Construction.gaussianIntegral k ψ a)) ∧
      Weil.Local.FunctionsMetaplectic.Construction.gaussianIntegral k ψ a ≠ 0 ∧ Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ a ^ 8 = 1) ∧

    (∀ (φ : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : Weil.Local.FunctionsMetaplectic.Construction.Position k n),
      Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure k n ψ)
        (Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure k n ψ) φ.val) x = φ.val (-x)) ∧
    Function.Surjective (Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection k n ψ) ∧
    ∃ (m : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k n → Weil.Local.FunctionsMetaplectic.Construction.Metaplectic k n ψ)
      (u : Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix k n → Weil.Local.FunctionsMetaplectic.Construction.Metaplectic k n ψ)
      (w : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic k n ψ),
      (∀ A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k n,
        Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection k n ψ (m A) = Weil.Local.Generators.Construction.leviSymplectic A) ∧
      (∀ B : Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix k n,
        Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection k n ψ (u B) = Weil.Local.Generators.Construction.quadraticSymplectic B) ∧
      Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection k n ψ w = Weil.Local.Generators.Construction.weylSymplectic k n ∧
      (∀ (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k n) (φ : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : Weil.Local.FunctionsMetaplectic.Construction.Position k n),
        (Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation k n ψ (m A) φ).val x =
          (Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k A) / Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ 1) *
          ((Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k A)))⁻¹ : ℂ) *
          φ.val (Matrix.mulVec (↑(A⁻¹) : Matrix (Fin n) (Fin n) k) x)) ∧
      (∀ (B : Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix k n) (φ : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : Weil.Local.FunctionsMetaplectic.Construction.Position k n),
        (Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation k n ψ (u B) φ).val x =
          ψ ((∑ i, ∑ j, x i * B.val i j * x j) / 2) * φ.val x) ∧
      (∀ (φ : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : Weil.Local.FunctionsMetaplectic.Construction.Position k n),
        (Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation k n ψ w φ).val x =
          (Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ n)⁻¹ *
          ∫ y : Weil.Local.FunctionsMetaplectic.Construction.Position k n,
            φ.val y * ψ (-(∑ i, x i * y i)) ∂(Weil.Local.FunctionsMetaplectic.Construction.positionMeasure k n ψ)) ∧
      (∀ g h : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic k n ψ,
        Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection k n ψ g = Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection k n ψ h →
        ∃ ε : ℂ, ε ^ 2 = 1 ∧
          ∀ φ : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k n,
            Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation k n ψ h φ = ε • Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation k n ψ g φ)

end LocalWeil

/- PoissonAutomorphy: repaired proposition mirrored from Statements/PoissonAutomorphy.lean. -/
namespace PoissonAutomorphy

open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

def Proposition : Prop := ∀
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (MpR MpF MpA : Type*) [Group MpR] [Group MpF] [Group MpA]
    (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA) (γ : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ),
    let g := Theta.PoissonAutomorphyNormalizationData.realBlocks γ
    (∀ f : Theta.PoissonAutomorphyNormalizationData.adelicSchwartz ι,
      Summable (fun x : ι → ℚ => ‖f.val (Theta.PoissonAutomorphyNormalizationData.diagonal x)‖)) ∧
    (∀ f : Theta.PoissonAutomorphyNormalizationData.adelicSchwartz ι,
      Theta.PoissonAutomorphyNormalizationData.thetaFunctional (D.rationalAction γ f) = Theta.PoissonAutomorphyNormalizationData.thetaFunctional f) ∧
    (∀ (φ : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ),
      Summable (fun x : ι → ℚ => ‖Theta.PoissonAutomorphyNormalizationData.thetaTerm φ Z z x‖)) ∧
    (∀ Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι,
      Theta.PoissonAutomorphyNormalizationData.halfDet g Z ^ 2 = (g.complexify.denominator Z.matrix).det) ∧
    (∀ (φ : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ),
      Theta.PoissonAutomorphyNormalizationData.theta (D.finiteAction γ φ) (g.transformSiegel Z) (g.jacobiChange Z z) =
        Theta.PoissonAutomorphyNormalizationData.halfDet g Z * (Theta.PoissonAutomorphyNormalizationData.quadraticFactor g Z z * Theta.PoissonAutomorphyNormalizationData.theta φ Z z))

end PoissonAutomorphy

end

end OAI.RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core
