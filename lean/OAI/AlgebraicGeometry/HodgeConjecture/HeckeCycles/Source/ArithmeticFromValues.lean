import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Projectors
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ProjectorPurity
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.CoefficientExtraction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceComparisonPlace

/-! # Arithmetic From Values -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArithmeticFromValues.CM.HeckeExtraction

/-! Construct projectors for the same actual source Hecke action and
extract its theta classes from proved ordinary-character arithmetic.
The arithmetic premise is discharged by the source GeometricTheta parameter theorem. -/

open scoped Classical TensorProduct BigOperators
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ScalarConjugate.CM.Projectors

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
  (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (W : Geometric.ThetaWitness.CM.Witness D hg hq hIsogenyQuotient)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q)
  (hcop : Nat.Coprime q D.pel.denominator) (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
  (fullSide : Fin s → Bool)
  (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)) (hv : v.val 1 = true)

local notation "AM" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.comparisonModel D.pel hg j hcop
local notation "idx" => fun i => W.action.basis
  (Subtype.val (Neighbor.Types.CM.integralType D.pel.reference.distinguished fullSide i))
local notation "θ" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaBettiClass.CM.classMap D hg hq hIsogenyQuotient W
local notation "ιE" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceComparisonPlace.CM.SourceClosureChoice.embedding E D.pel j

def Arithmetic : Prop :=
  ∀ (χ : AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) (P : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification D.pel.H1)),
    (∀ h, Commute P ((W.action.cohomologyAction h).baseChange ℂ)) →
    LinearMap.range P ≤ HeckeCharacters.CM.Projectors.jointSpace (fun h => (W.action.cohomologyAction h).baseChange ℂ)
      (fun h => j.complexClosure (χ h)) →
    (∃ φ : D.sphericalInputs, P (θ φ) ≠ 0) →
    ∀ τ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ), ∃ z b : CMExtraction.ParameterChoices.Qbar,
      ‖j.complexClosure z‖ = 1 ∧
      (∃ n : ℕ, 0 < n ∧ (b ^ 3 * z) ^ n = 1) ∧
      (∀ i : Fin 3, τ (χ (idx i)) =
        (![(q : CMExtraction.ParameterChoices.Qbar) * b * (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure + (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure)⁻¹ + z),
          (q : CMExtraction.ParameterChoices.Qbar) * b ^ 2 * (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure * (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure)⁻¹ +
            CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure * z + (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure)⁻¹ * z),
          b ^ 3 * z] : Fin 3 → CMExtraction.ParameterChoices.Qbar) i) ∧
      NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q j.iota z = (ComplexMultiplication.SignSwitch.CM.signValue (v.val (CMExtraction.ParameterChoices.restriction E ιE τ)) : ℚ) * (-3 / 2)

include hv in
theorem extraction :
    letI : CommRing (AbelianScheme.TateComparison.HeckeKernel.Hecke s q) := TateComparisonAction.CM.commutativeHeckeRing s q hElementaryDivisors
    ∀ (R : (AM).HeckeRealization (AbelianScheme.TateComparison.HeckeKernel.Hecke s q))
    (_hbetti : (AM).bettiHecke D.pel.complexEmbedding R = (fun h => W.action.cohomologyAction h))
    (hHodgeDecomposition : CMExtraction.Mem.HodgeDecompositionInput)
    (_hE07 : PELModuli.IntegralModel.Albanese.ConstructionInput) (_hE08 : PELModuli.IntegralModel.AlbaneseCohomology.HodgeComparisonInput)
    (_hμ : D.pel.reference.μ = E.val.toRingHom)
    (_hc : Constructed.Comparison.CM.Conclusion AM j.fieldInClosure j.complexClosure j.iota R idx)
    (_harith : Arithmetic E D hg hq hIsogenyQuotient W j fullSide v)
    (_hP422 : MatchedLevelExtraction.CM.Construction.CMExtractionInput.{0, 0, 0, 0}),
    ∀ φ : D.sphericalInputs, θ φ ∈ MatchedLevelExtraction.CM.Construction.lineImageSpan E v (CMExtraction.Intrinsic.Base.nativeH1 D hHodgeDecomposition hg) := by
  let : CommRing (AbelianScheme.TateComparison.HeckeKernel.Hecke s q) := TateComparisonAction.CM.commutativeHeckeRing s q hElementaryDivisors
  intro R hbetti hHodgeDecomposition hConstruction hHodgeComparison hμ hc harith hCMExtraction
  let : FiniteDimensional ℚ D.pel.H1 := CMExtraction.Intrinsic.Base.native_betti_finite D hg
  obtain ⟨F, hF, hGal, hEF, hFalg, n, p, χ, hid, hcoeff, hH, hComm, hOcc, hSum, hSpace, hConj⟩ :=
    Projectors.CM.Hecke.exists_projectors E D hg hq hIsogenyQuotient W hHodgeDecomposition j.complexClosure hConstruction hHodgeComparison hElementaryDivisors
  let : NumberField F := hF
  let : IsGalois ℚ F := hGal
  apply CoefficientExtraction.CM.extraction E F hEF hFalg v hv j.complexClosure ιE
    (ReferenceComparisonPlace.CM.SourceClosureChoice.complex_compatibility E D.pel j hg hμ)
    (CMExtraction.Intrinsic.Base.nativeH1 D hHodgeDecomposition hg) θ p hid hH
    (Geometric.ThetaBettiClass.CM.holomorphic D hg hq hIsogenyQuotient W hHodgeDecomposition) hOcc hSum _ hCMExtraction
  intro i σ
  obtain ⟨τ, hτ, hQ, hRange⟩ := hConj i σ
  let Q := ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients F D.pel.H1 D.pel.H1
    (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ F (D.pel.H1 →ₗ[ℚ] D.pel.H1) σ (p i))
  have hPne : ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients F D.pel.H1 D.pel.H1 (p i) ≠ 0 := by
    obtain ⟨φ, hφ⟩ := hOcc i
    intro hz
    exact hφ (LinearMap.congr_fun hz (θ φ))
  have hQne : LinearMap.range Q ≠ ⊥ := by
    intro hz
    exact ScalarConjugate.CM.Projectors.conjugateSpace_ne_bot F (p i) σ hPne
      ((ScalarConjugate.CM.Projectors.conjugated_range_eq_conjugateSpace F (p i) σ).symm.trans hz)
  have hχne : HeckeCharacters.CM.Projectors.jointSpace (fun h => (W.action.cohomologyAction h).baseChange ℂ)
      (fun h => j.complexClosure (χ i h)) ≠ ⊥ := by
    intro hz
    exact hPne (LinearMap.range_eq_bot.mp ((hSpace i).trans hz))
  obtain ⟨z, b, hnorm, hcentral, hvalues, hsign⟩ :=
    harith (χ i) (ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients F D.pel.H1 D.pel.H1 (p i))
      (hComm i) (hSpace i).le (hOcc i) τ
  have hp := ProjectorPurity.CM.bounds D hg j hcop hElementaryDivisors W.action fullSide
    R hbetti hHodgeDecomposition hc (χ i) hχne τ Q hQ hRange hQne b z hnorm hcentral hvalues
    (v.val (CMExtraction.ParameterChoices.restriction E ιE τ)) hsign
  exact ⟨τ, hτ, hp.1.mp, hp.2.mp⟩

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArithmeticFromValues.CM.HeckeExtraction

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArithmeticFromValues.CM

/-! Convert full ordinary parameter values to the arithmetic proposition
on an abstract theta witness, before specializing its geometric data. -/

open scoped Classical TensorProduct BigOperators
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ScalarConjugate.CM.Projectors

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
  (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (W : Geometric.ThetaWitness.CM.Witness D hg hq hIsogenyQuotient)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q)
  (hcop : Nat.Coprime q D.pel.denominator) (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
  (fullSide : Fin s → Bool)
  (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)) (hv : v.val 1 = true)

local notation "AM" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.comparisonModel D.pel hg j hcop
local notation "idx" => fun i => W.action.basis
  (Subtype.val (Neighbor.Types.CM.integralType D.pel.reference.distinguished fullSide i))
local notation "θ" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaBettiClass.CM.classMap D hg hq hIsogenyQuotient W
local notation "ιE" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceComparisonPlace.CM.SourceClosureChoice.embedding E D.pel j

theorem arithmetic
    (hvalues :
  ∀ (χ : AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) (P : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification D.pel.H1)),
    (∀ h, Commute P ((W.action.cohomologyAction h).baseChange ℂ)) →
    LinearMap.range P ≤ HeckeCharacters.CM.Projectors.jointSpace (fun h => (W.action.cohomologyAction h).baseChange ℂ)
      (fun h => j.complexClosure (χ h)) →
    ∀ φ : D.sphericalInputs, P (θ φ) ≠ 0 →
    ∀ τ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ), ∃ z b : CMExtraction.ParameterChoices.Qbar,
      z ≠ 0 ∧ b ≠ 0 ∧ (∀ γ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ), ‖j.complexClosure (γ z)‖ = 1) ∧
      (∃ n : ℕ, 0 < n ∧ (b ^ 3 * z) ^ n = 1) ∧
      (∀ i : Fin 3, τ (χ (idx i)) =
        (![(q : CMExtraction.ParameterChoices.Qbar) * b * (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure + (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure)⁻¹ + z),
          (q : CMExtraction.ParameterChoices.Qbar) * b ^ 2 * (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure * (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure)⁻¹ +
            CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure * z + (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure)⁻¹ * z),
          b ^ 3 * z] : Fin 3 → CMExtraction.ParameterChoices.Qbar) i) ∧
      NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q j.iota z = (ComplexMultiplication.SignSwitch.CM.signValue (v.val (CMExtraction.ParameterChoices.restriction E ιE τ)) : ℚ) * (-3 / 2)) :
    HeckeExtraction.Arithmetic E D hg hq hIsogenyQuotient W j fullSide v := by
  intro χ P hP hspace hocc τ
  obtain ⟨φ, hφ⟩ := hocc
  obtain ⟨z, b, _hz, _hb, hnorm, hcentral, hvalues, hsign⟩ :=
    hvalues χ P hP hspace φ hφ τ
  exact ⟨z, b, by simpa only [AlgEquiv.one_apply] using hnorm 1, hcentral, hvalues, hsign⟩

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArithmeticFromValues.CM

end

end OAI
