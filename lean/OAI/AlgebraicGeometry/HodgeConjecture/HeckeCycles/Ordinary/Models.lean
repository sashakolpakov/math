import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticModels
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Models
import OAI.AlgebraicGeometry.PELModuli.CMPoints.DualityPairing

/-! # Models -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Models.CM

noncomputable section

/-! Apply the named CMPoints prerequisite to the actual integral universal
family supplied by IntegralModel. The model contains that family and its component
Albanese schemes; ordinary points and split coordinates are conclusions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticModels.CM

universe u v

/-- CMPoints's full arithmetic and ordinary-reduction conclusion, expressed
using its native block and polarization definitions. -/
def OrdinaryConclusion
    (E K : Type) [Field E] [NumberField E] [Algebra ℚ E]
    [IsGalois ℚ E] [NumberField.IsCMField E] [Field K] [NumberField K]
    (M : PELModuli.CMPoints.Models.RankThreePELModel E K)
    {ι : Type u} [Fintype ι] (L : ι → Type v)
    [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    (excluded : Finset ℕ) (bound : ℕ) : Prop :=
    ∃ (q : ℕ) (hq : q.Prime),
      letI : Fact q.Prime := ⟨hq⟩
      bound < q ∧ q ∉ excluded ∧
      PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt E q ∧ PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt K q ∧
      PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt M.arithmetic.extension.carrier q ∧
      (∀ i, PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt (L i) q) ∧
      ∃ j : M.QadicChoice q,
        j.HasSplitCoordinates M.extendedEmbedding ∧
        ∃ R : M.GoodIntegralReduction q j,
          (∀ a : M.Family,
            IsOpen (R.ordinaryLocus a) ∧ ∀ x : R.geom a,
              Dense {y : connectedComponent x | R.IsOrdinary a y.val}) ∧
          ∃ chosen : Set Gal(E/ℚ),
            let c : Gal(E/ℚ) :=
              (NumberField.IsCMField.complexConj E).restrictScalars ℚ
            c ∈ chosen ∧ (∀ τ, τ ∈ chosen ↔ c * τ ∉ chosen) ∧
            (∀ (a : M.Family) (x : R.geom a) (τ : Gal(E/ℚ)),
              PELModuli.CMPoints.BlocksProjectors.BlockHasHeight (R.fiberAbelian a x) (R.fiberAction a x)
                (j.localCharacter M.extendedEmbedding τ) 3 ∧
              PELModuli.CMPoints.DualityPairing.PolarizationDuality (R.fiberPolarized a x) (R.fiberAction a x)
                (j.localCharacter M.extendedEmbedding τ)
                (j.localCharacter M.extendedEmbedding (c * τ))) ∧
            (∀ (a : M.Family) (x : R.geom a),
              R.HasLieRank a x c 1 ∧ ∀ τ ∈ chosen, τ ≠ c →
                R.HasLieRank a x τ 0 ∨ R.HasLieRank a x τ 3)

/-- The named CMPoints prerequisite, with its full conclusion. The expanded
height and polarization predicates are definitionally equal to the full
compiled specification, as checked in `HeckeCyclesCMPointsInputAudit`. No theorem
placeholder is invoked. -/
def CMPointsInput : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Algebra ℚ E]
    [IsGalois ℚ E] [NumberField.IsCMField E] [Field K] [NumberField K]
    (M : PELModuli.CMPoints.Models.RankThreePELModel E K) (_hM : M.HasPrescribedBallPeriods)
    {ι : Type u} [Fintype ι] (L : ι → Type v)
    [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    (excluded : Finset ℕ) (bound : ℕ),
      OrdinaryConclusion E K M L excluded bound

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [IsGalois ℚ E] [NumberField.IsCMField E] [Field K] [NumberField K]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
  (iota : E →+* K) (κ : K →+* ℂ) (N : ℕ)
  (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N)

/-- A one-family CMPoints model made from the literal integral spread and
component schemes; no existence or ordinary-locus assertion is a field. -/
def singletonModel
    (B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ)
    (T : PELModuli.IntegralModel.PEL.Has.IntegralPELSpread P iota κ N M.space M.universal B)
    (r : ℕ) (D : PELModuli.IntegralModel.Components.ComponentAlbaneseData T.toOver r) (e : (∐ D.S) ≅ T.toOver) :
    PELModuli.CMPoints.Models.RankThreePELModel E K where
  s := s
  familyCount := 1
  iota := iota
  complexEmbedding := κ
  arithmetic := B
  datum := fun _ => P
  level := fun _ => N
  moduli := fun _ => M
  integral := fun _ => T
  componentCount := fun _ => r
  components := fun _ => D
  decomposition := fun _ => e

/-- IntegralModel's conclusions supply all the geometric hypotheses of CMPoints
for this same family. -/
theorem ordinary_model_from_integral
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hP : P.IsAdmissible) (hEmb : κ.comp iota = P.μ)
    (hN : PELModuli.IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel P N)
    (hM : M.IsFine) (hball : M.HasProjectiveBallComponents κ)
    (hintegral : ArithmeticModels.CM.IntegralConclusion P iota κ N M) :
    ∃ (B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ)
      (T : PELModuli.IntegralModel.PEL.Has.IntegralPELSpread P iota κ N M.space M.universal B)
      (r : ℕ) (D : PELModuli.IntegralModel.Components.ComponentAlbaneseData T.toOver r) (e : (∐ D.S) ≅ T.toOver),
      (singletonModel P iota κ N M B T r D e).HasPrescribedBallPeriods := by
  obtain ⟨B, _hunit, T, hclassifies, hsmooth, hproper, hprojective,
    r, D, e, hcomponents, _hbetti, _hgeneration⟩ := hintegral
  refine ⟨B, T, r, D, e, ?_⟩
  refine ⟨hs, hdegree, fun _ => ?_⟩
  refine ⟨hP, hEmb, hN, hM, hball, hclassifies, hsmooth, hproper, hprojective, ?_⟩
  intro j
  exact ⟨(hcomponents j).1, (hcomponents j).2.1,
    (hcomponents j).2.2.1, (hcomponents j).2.2.2.1⟩

/-- The split prime, local coordinates, ordinary locus, heights and duality
are obtained by applying CMPoints to this exact integral family. -/
theorem good_prime_from_integral
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hP : P.IsAdmissible) (hEmb : κ.comp iota = P.μ)
    (hN : PELModuli.IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel P N)
    (hM : M.IsFine) (hball : M.HasProjectiveBallComponents κ)
    (hintegral : ArithmeticModels.CM.IntegralConclusion P iota κ N M)
    (h_CMPoints : CMPointsInput.{u, v})
    {ι : Type u} [Fintype ι] (L : ι → Type v)
    [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    (excluded : Finset ℕ) (bound : ℕ) :
    ∃ (B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ)
      (T : PELModuli.IntegralModel.PEL.Has.IntegralPELSpread P iota κ N M.space M.universal B)
      (r : ℕ) (D : PELModuli.IntegralModel.Components.ComponentAlbaneseData T.toOver r) (e : (∐ D.S) ≅ T.toOver),
      let Q := singletonModel P iota κ N M B T r D e
      Q.HasPrescribedBallPeriods ∧ OrdinaryConclusion E K Q L excluded bound := by
  obtain ⟨B, T, r, D, e, hQ⟩ := ordinary_model_from_integral P iota κ N M
    hs hdegree hP hEmb hN hM hball hintegral
  exact ⟨B, T, r, D, e, hQ, h_CMPoints E K _ hQ L excluded bound⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Models.CM
