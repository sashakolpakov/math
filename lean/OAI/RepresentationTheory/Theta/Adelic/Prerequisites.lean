import OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData
import OAI.Geometry.ComplexBall.CotangentBundle
import OAI.RepresentationTheory.Theta.Definitions
import OAI.RepresentationTheory.Weil.Local.Formulas
import OAI.RepresentationTheory.Weil.UnitarySplitting.DualPairSplitting
import OAI.RepresentationTheory.Weil.AdelicSplitting.No
import OAI.Topology.Pontryagin.CharacterExtension
import OAI.NumberTheory.Adeles.RelativeModulus
import OAI.LieTheory.Semisimple.CharacterTrivialityEq
import OAI.GroupTheory.LinearGroups.SpecialLinearPerfect

/-! # Prerequisites -/

namespace OAI.RepresentationTheory.Theta.Adelic.Prerequisites

noncomputable section

/-! Full designated prerequisite propositions for AdelicTheta. No statement stub is
imported. ArithmeticQuotient uses its shared concrete definitions and induced cone topology;
CotangentBundle and CompletedTheta use their definition-identical construction namespaces. Every
argument and conclusion of each designated proposition is retained. -/

open scoped _root_.NumberField _root_.Topology BigOperators _root_.Manifold ContDiff _root_.Matrix BoundedContinuousFunction
universe u v

section ArithmeticQuotient
open OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData

/-- Full ArithmeticQuotient proposition at 11c9f9e466dcfe73ab3bb02dcba1961d8aaea9f7. -/
def ArithmeticQuotientInput : Prop :=
  ∀ {E : Type u} [Field E] [NumberField E] [NumberField.IsCMField E]
    [IsGalois ℚ E]
    (μ : E →+* ℂ)

    (_h_other_place :
      ∃ ν : E →+* ℂ,
        ν ≠ μ ∧ ν ≠ (starRingEnd ℂ).comp μ),
    ∃ b : E,
      NumberField.IsCMField.complexConj E b = b ∧
      b ≠ 0 ∧

      (μ b).re < 0 ∧
      (∀ ν : E →+* ℂ,
        ν ≠ μ → ν ≠ (starRingEnd ℂ).comp μ →
          0 < (ν b).re) ∧

      (∀ x : Geometry.ComplexBall.ArithmeticQuotientEquationsData.Vec E,
        (∀ y : Geometry.ComplexBall.ArithmeticQuotientEquationsData.Vec E, Geometry.ComplexBall.ArithmeticQuotientEquationsData.hermitian b x y = 0) → x = 0) ∧
      (∀ x : Geometry.ComplexBall.ArithmeticQuotientEquationsData.Vec E, Geometry.ComplexBall.ArithmeticQuotientEquationsData.hermitian b x x = 0 → x = 0) ∧

      (∀ N₀ : ℕ, 0 < N₀ →
        ∃ N : ℕ, 0 < N ∧ N₀ ∣ N ∧
          (∀ g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.Mat E, Geometry.ComplexBall.ArithmeticQuotientEquationsData.principalLevel b N g →
            ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) ∧
          ∃ R : Setoid (Geometry.ComplexBall.ArithmeticQuotientEquationsData.NegativeVectors b μ),
            (∀ z w, R.r z w ↔ Geometry.ComplexBall.ArithmeticQuotientEquationsData.orbitRelation b μ N z w) ∧
            CompactSpace (Quotient R) ∧
            T2Space (Quotient R) ∧
            SecondCountableTopology (Quotient R) ∧
            ConnectedSpace (Quotient R) ∧
            ∃ atlas : ChartedSpace (Fin 2 → ℂ) (Quotient R),
              letI := atlas
              IsManifold 𝓘(ℂ, Fin 2 → ℂ) 1 (Quotient R) ∧

              ∀ z : Geometry.ComplexBall.ArithmeticQuotientEquationsData.NegativeVectors b μ,
                MDifferentiableAt
                  𝓘(ℂ, Geometry.ComplexBall.ArithmeticQuotientEquationsData.Vec ℂ) 𝓘(ℂ, Fin 2 → ℂ)
                  (Geometry.ComplexBall.ArithmeticQuotientEquationsData.projection b μ R z) z.val ∧
                Function.Surjective
                  (mfderiv
                    𝓘(ℂ, Geometry.ComplexBall.ArithmeticQuotientEquationsData.Vec ℂ) 𝓘(ℂ, Fin 2 → ℂ)
                    (Geometry.ComplexBall.ArithmeticQuotientEquationsData.projection b μ R z) z.val))

end ArithmeticQuotient

section CotangentBundle
open OAI.Geometry.ComplexBall.CotangentBundle

/-- Full CotangentBundle proposition at 3a4d41f3e609cabae322f8bc1462b089811c5210. -/
def CotangentBundleInput : Prop :=
  ∀ {B : Type u} {A : Type v} [CommSemiring B] [CommGroup A]
    (C : Geometry.ComplexBall.CotangentBundle.BundleCalculus B A)
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
    Geometry.ComplexBall.CotangentBundle.projectiveCotangent C L Q = C.line L * C.dual Q

end CotangentBundle

section CompletedTheta
open scoped _root_.Matrix.Norms.Elementwise
open _root_.Matrix OAI.RepresentationTheory.Theta.Definitions

/-- Full CompletedTheta proposition at 1802c76971ce2806b747860c101adb3f0ca7470b. -/
def ThetaInput : Prop :=
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
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
      Definitions.theta Lnew φnew (g.transformSiegel Z).matrix
          (g.jacobiChange Z z) =
        halfDet Z *
          (Complex.exp (g.thetaCorrectionForm Z z z) *
            Definitions.theta L φ Z.matrix z)),
    (∀ a : ℕ,
      ContDiffOn ℝ ⊤ (Definitions.completedTensor L φ a) Definitions.siegelDomain) ∧

    (∀ (a : ℕ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι)
        (σ : Equiv.Perm (Fin a)) (v : Fin a → (ι → ℂ)),
      Definitions.completedTensor L φ a Z.matrix (fun i => v (σ i)) =
        Definitions.completedTensor L φ a Z.matrix v) ∧

    (∀ (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ),
      Definitions.completedTheta Lnew φnew (g.transformSiegel Z).matrix
          (g.jacobiChange Z z) =
        halfDet Z * Definitions.completedTheta L φ Z.matrix z) ∧

    (∀ (a : ℕ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι)
        (v : Fin a → (ι → ℂ)),
      Definitions.completedTensor Lnew φnew a (g.transformSiegel Z).matrix
          (fun i => g.jacobiChange Z (v i)) =
        halfDet Z * Definitions.completedTensor L φ a Z.matrix v)

end CompletedTheta

section LocalWeil
open _root_.MeasureTheory Filter

/-- Full LocalWeil proposition at 05f4395ff6dccb2437ab0f7baace7c45de522789. -/
def LocalWeilInput : Prop :=
  ∀
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

section UnitarySplitting

/-- Full UnitarySplitting proposition at b4046dd146f46f308cc826d8bed018ce9135048d. -/
def UnitarySplittingInput : Prop :=
  ∀
    (F E : Type)
    [NormedField F] [NormedField E] [Algebra F E]
    [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
    [CompleteSpace E] [LocallyCompactSpace E]
    [FiniteDimensional F E]
    [MeasurableSpace F] [BorelSpace F]
    (_hF : ¬ DiscreteTopology F)
    (_hE : ¬ DiscreteTopology E)
    (_hEmbedding : Continuous (algebraMap F E))
    (_hQuadratic : Module.finrank F E = 2)
    (σ : E ≃ₐ[F] E)
    (_hConjugation : ∃ z : E, σ z ≠ z)
    (m n : ℕ)
    (H : Matrix (Fin m) (Fin m) E)
    (K : Matrix (Fin n) (Fin n) E)
    (_hHermitian : ∀ i j, H j i = σ (H i j))
    (_hSkewHermitian : ∀ i j, K j i = -σ (K i j))
    (_hHNondegenerate : H.det ≠ 0)
    (_hKNondegenerate : K.det ≠ 0)
    (ψ : AddChar F ℂ)
    (_hψContinuous : Continuous (fun x : F => ψ x))
    (_hψUnitary : ∀ x : F, ‖ψ x‖ = 1)
    (_hψNontrivial : ∃ x : F, ψ x ≠ 1)
    (_characters : Weil.UnitarySplitting.Characters.Construction.SplittingCharacters F E m n),
    Nonempty (Weil.UnitarySplitting.Oscillator.Construction.SymplecticFrame σ H K) ∧
    ∀ c : Weil.UnitarySplitting.Oscillator.Construction.SymplecticFrame σ H K,
      IsTopologicalGroup (Weil.UnitarySplitting.Oscillator.Construction.CircleExtension σ H K c ψ) ∧
      Function.Surjective (Weil.UnitarySplitting.Oscillator.Construction.circleProjection σ H K c ψ) ∧
      Continuous (Weil.UnitarySplitting.Oscillator.Construction.circleScalar σ H K c ψ) ∧
      Function.Injective (Weil.UnitarySplitting.Oscillator.Construction.circleScalar σ H K c ψ) ∧
      (∀ a : Weil.UnitarySplitting.Oscillator.Construction.CircleExtension σ H K c ψ,
        Weil.UnitarySplitting.Oscillator.Construction.circleProjection σ H K c ψ a = 1 ↔
          ∃ z : Circle, Weil.UnitarySplitting.Oscillator.Construction.circleScalar σ H K c ψ z = a) ∧
      ∃ splitting : (Weil.UnitarySplitting.DualPair.Construction.unitaryGroup σ H × Weil.UnitarySplitting.DualPair.Construction.unitaryGroup σ K) →ₜ*
          Weil.UnitarySplitting.Oscillator.Construction.CircleExtension σ H K c ψ,
        ∀ g : Weil.UnitarySplitting.DualPair.Construction.unitaryGroup σ H × Weil.UnitarySplitting.DualPair.Construction.unitaryGroup σ K,
          Weil.UnitarySplitting.Oscillator.Construction.circleProjection σ H K c ψ (splitting g) =
            Weil.UnitarySplitting.DualPair.Construction.continuousDualPairAction σ H K g

end UnitarySplitting

section AdelicSplitting

/-- Full AdelicSplitting proposition at 2fde7f1772821f725e25d8660cc2538744ade98e. -/
def AdelicSplittingInput : Prop :=
  ∀
    (F : Type) [Field F] [NumberField F]
    (d : F) (hQuadratic : d ≠ 0 ∧ ¬ IsSquare d)
    (n m : ℕ)
    (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (_hHermitian : H.val.conjTranspose = H.val)
    (_hSkewHermitian : K.val.conjTranspose = -K.val)
    (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d n m)
    (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d n m H K)
    (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d n m H K hQuadratic.1 C P),
    (∀ g : Weil.AdelicSplitting.Integral.Construction.AdelicDualPair F H.val K.val,
      Weil.AdelicSplitting.Vacuum.Construction.globalProjection F (n * m) C.ψ
          (Weil.AdelicSplitting.Assembly.Construction.constructedAdelicLift F d n m H K hQuadratic.1 C P D g) =
        Weil.AdelicSplitting.Assembly.Construction.adelicDualPairAction F d n m H K hQuadratic.1 C P D g) ∧
    (∀ v (g : Weil.AdelicSplitting.Integral.Construction.LocalUnitary F H.val v × Weil.AdelicSplitting.Integral.Construction.LocalUnitary F K.val v),
      Weil.AdelicSplitting.Assembly.Construction.constructedAdelicLift F d n m H K hQuadratic.1 C P D
          (Weil.AdelicSplitting.Integral.Construction.includeUnitaryPlace F H.val K.val v g) =
        Weil.AdelicSplitting.Vacuum.Construction.globalInclude F (n * m) C.ψ v (D.atPlace v g)) ∧
    ∃ r : Weil.Local.FunctionsMetaplectic.Construction.Symplectic F (n * m) →* Weil.AdelicSplitting.Vacuum.Construction.GlobalCover F (n * m) C.ψ,
      (∀ γ a, (γ, a) ∈ Weil.AdelicSplitting.Rational.Construction.rationalGraph F (n * m) C.ψ ↔ r γ = a) ∧
      (∀ γ, Weil.AdelicSplitting.Vacuum.Construction.globalProjection F (n * m) C.ψ (r γ) =
        Weil.AdelicSplitting.Vacuum.Construction.rationalSymplectic F (n * m) γ) ∧
      (∀ g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val,
        Weil.AdelicSplitting.Assembly.Construction.constructedAdelicLift F d n m H K hQuadratic.1 C P D
            (Weil.AdelicSplitting.Integral.Construction.rationalPair F H.val K.val g) =
          r (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational g))

end AdelicSplitting

section CharacterExtension

/-- Full CharacterExtension proposition at 8842447a1bef783684a33945815adbbad82d702b. -/
def CharacterExtensionInput : Prop :=
  ∀
    {G : Type*}
    [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (H : Subgroup G)
    (_hH : IsClosed (H : Set G))
    (χ : H →ₜ* Circle),
    ∃ χG : G →ₜ* Circle, ∀ h : H, χG (h : G) = χ h

end CharacterExtension

section CompletionFactors

/-- Full CompletionFactors proposition at a7c3ce9fde52aace12471f6df1ffe765c42ea968. -/
def CompletionFactorsInput : Prop :=
  ∀
    (F E : Type*)
    [Field F] [NumberField F]
    [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E]
    (hQuadratic : Module.finrank F E = 2),
    IsCompact
      {c : NumberTheory.Adeles.LocalCompletions.CompletionFactors.IdeleClass E | NumberTheory.Adeles.RelativePrincipal.CompletionFactors.relativeIdeleClassNorm hQuadratic c = 1}

end CompletionFactors

section CharacterTriviality

/-- Full CharacterTriviality proposition at 327d4ceb0ba5615ab70a0fbd2689d4bfcb9106c1. -/
def CharacterTrivialityInput : Prop :=
  ∀
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (G : Type*) [Group G] [TopologicalSpace G]
    [T2Space G] [SecondCountableTopology G] [ConnectedSpace G]
    [ChartedSpace E G] [IsManifold (𝓘(ℝ, E)) ∞ G]
    [LieGroup (𝓘(ℝ, E)) ∞ G]
    [LieAlgebra.IsSemisimple ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)]
    (χ : ContinuousMonoidHom G Circle),
    ∀ g : G, χ g = 1

end CharacterTriviality

section Perfect

/-- Full SL3Perfect proposition at 37e36a75617f2a0a4a0b926ccf6750245c65f313. -/
def PerfectInput : Prop :=
  ∀
    (k : Type u) [Field k],
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) k)

end Perfect

section Characters

/-- Full SL3Perfect proposition at 37e36a75617f2a0a4a0b926ccf6750245c65f313. -/
def CharactersInput : Prop :=
  ∀
    (k : Type u) [Field k]
    (A : Type v) [CommGroup A]
    (χ : Matrix.SpecialLinearGroup (Fin 3) k →* A),
    χ = 1

end Characters

/-- The full designated propositions, without local-splitting, global
compatibility, smoothness, or descent assumptions added to their conclusions. -/
structure Inputs : Prop where
  ArithmeticQuotient : ArithmeticQuotientInput.{u}
  CotangentBundle : CotangentBundleInput.{u, v}
  CompletedTheta : ThetaInput.{u}
  LocalWeil : LocalWeilInput
  UnitarySplitting : UnitarySplittingInput
  AdelicSplitting : AdelicSplittingInput
  CharacterExtension : CharacterExtensionInput.{u}
  CompletionFactors : CompletionFactorsInput.{u, v}
  CharacterTriviality : CharacterTrivialityInput.{u, v}
  Perfect : PerfectInput.{u}
  Characters : CharactersInput.{u, v}

end

end OAI.RepresentationTheory.Theta.Adelic.Prerequisites
