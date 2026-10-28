import OAI.AlgebraicGeometry.PELModuli.CMPoints.Models
import OAI.AlgebraicGeometry.PELModuli.CMPoints.DualityPairing
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsReductionAdapter
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsModelLabels

/-! # CM Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPoints.Construction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

def GeometricConclusion
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K]
    {M : PELModuli.CMPoints.Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime] {j : M.QadicChoice q}
    (R : M.GoodIntegralReduction q j) : Prop :=
  (∀ a : M.Family, IsOpen (R.ordinaryLocus a) ∧
    ∀ x : R.geom a, Dense {y : connectedComponent x | R.IsOrdinary a y.val}) ∧
  ∃ chosen : Set Gal(E/ℚ),
    let c := PELModuli.CMPoints.Arithmetic.rationalConjugation E
    c ∈ chosen ∧
    (∀ τ, τ ∈ chosen ↔ c * τ ∉ chosen) ∧
    (∀ (a : M.Family) (x : R.geom a) (τ : Gal(E/ℚ)),
      PELModuli.CMPoints.BlocksProjectors.BlockHasHeight (R.fiberAbelian a x) (R.fiberAction a x)
          (j.localCharacter M.extendedEmbedding τ) 3 ∧
        PELModuli.CMPoints.DualityPairing.PolarizationDuality (R.fiberPolarized a x) (R.fiberAction a x)
          (j.localCharacter M.extendedEmbedding τ) (j.localCharacter M.extendedEmbedding (c * τ))) ∧
    (∀ (a : M.Family) (x : R.geom a),
      R.HasLieRank a x c 1 ∧
      ∀ τ ∈ chosen, τ ≠ c → R.HasLieRank a x τ 0 ∨ R.HasLieRank a x τ 3)

/-- The complete CMPoints graph input, including arbitrarily large primes,
all excluded fields and primes, and every geometric conclusion. -/
def CMPointsInput : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Algebra ℚ E]
    [IsGalois ℚ E] [NumberField.IsCMField E] [Field K] [NumberField K]
    (M : PELModuli.CMPoints.Models.RankThreePELModel E K) (_hM : M.HasPrescribedBallPeriods)
    {I : Type u} [Fintype I] (L : I → Type v) [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    (excluded : Finset ℕ) (bound : ℕ),
    ∃ (q : ℕ) (hq : q.Prime),
      let _ : Fact q.Prime := ⟨hq⟩
      bound < q ∧ q ∉ excluded ∧ PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt E q ∧ PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt K q ∧
      PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt M.arithmetic.extension.carrier q ∧
      (∀ i, PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt (L i) q) ∧
      ∃ j : M.QadicChoice q, j.HasSplitCoordinates M.extendedEmbedding ∧
        ∃ R : M.GoodIntegralReduction q j, GeometricConclusion R

/-- Each resulting family has a native reduction with the original
integral source and the actual q-adic coefficient labels. -/
theorem nativeReductions_of_CMPointsInput (hCMPoints : CMPointsInput.{u, v})
    (E K : Type) [Field E] [NumberField E] [Algebra ℚ E]
    [IsGalois ℚ E] [NumberField.IsCMField E] [Field K] [NumberField K]
    (M : PELModuli.CMPoints.Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
    {I : Type u} [Fintype I] (L : I → Type v) [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    (excluded : Finset ℕ) (bound : ℕ) :
    ∃ (q : ℕ) (hq : q.Prime),
      let _ : Fact q.Prime := ⟨hq⟩
      bound < q ∧ q ∉ excluded ∧ PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt E q ∧ PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt K q ∧
      PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt M.arithmetic.extension.carrier q ∧
      (∀ i, PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt (L i) q) ∧
      ∃ (j : M.QadicChoice q) (hsplit : j.HasSplitCoordinates M.extendedEmbedding)
        (R : M.GoodIntegralReduction q j), GeometricConclusion R ∧
        ∃ labels : (Fin M.s × Bool) ≃ Gal(E/ℚ),
          labels (⟨0, hM.1⟩, false) = PELModuli.CMPoints.Arithmetic.rationalConjugation E ∧
          ∃ hlabels : ∀ (w : Fin M.s) (b : Bool), labels (w, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (w, b),
            ∀ a : M.Family,
              (CMPointsReductionAdapter.Construction.l45SplitPELReduction M hM j hsplit R labels hlabels a).integral = M.integral a ∧
              (CMPointsReductionAdapter.Construction.l45SplitPELReduction M hM j hsplit R labels hlabels a).specialFiber = R.specialFiber a := by
  obtain ⟨q, hq, hbound, hex, hE, hK, hExt, hL, j, hsplit, R, hgeom⟩ :=
    hCMPoints E K M hM L excluded bound
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨chosen, hc, hchosen, _, _⟩ := hgeom.2
  obtain ⟨labels, hactive, hlabels, _, _⟩ := CMPointsModelLabels.Construction.exists_l45ModelLabels M hM chosen hc hchosen
  exact ⟨q, hq, hbound, hex, hE, hK, hExt, hL, j, hsplit, R, hgeom,
    labels, hactive, hlabels, fun a =>
      ⟨CMPointsReductionAdapter.Construction.l45SplitPELReduction_integral M hM j hsplit R labels hlabels a,
        CMPointsReductionAdapter.Construction.l45SplitPELReduction_specialFiber M hM j hsplit R labels hlabels a⟩⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPoints.Construction
