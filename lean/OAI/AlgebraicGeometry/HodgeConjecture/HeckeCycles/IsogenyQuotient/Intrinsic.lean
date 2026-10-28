import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.ReferenceRealization
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.Realization
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.DescentIntrinsic
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.PairLabels

/-! # Intrinsic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.Intrinsic.CM

noncomputable section

/-! Apply the complete native IsogenyQuotient construction and transport its
classified correspondences to the identical IntegralModel spread. The quotient
input is supplied by the proved full FiniteDescent theorem. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

variable {E K L : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  [Field K] [NumberField K] [Field L] [NumberField L] {κ : L →+* ℂ}
  {s N q : ℕ} [NeZero N] [Fact q.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
  (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine)
  (κ₀ : K →+* ℂ) (hC : M.HasProjectiveBallComponents κ₀)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (aE : E →+* L) (hsplit : j.HasSplitCoordinates aE)
  (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
  (labels : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ))
  (hlabels : ∀ i, labels (Sum.swap i) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels i)
  (hcop : Nat.Coprime q N) (hpol : Nat.Coprime q (∏ i, P.polarizationType i))
  (χ : Fin s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q])
  (hχ : ∀ v, χ (v, false) = j.localCharacter aE (labels (.inl v)))
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ₀}
  (V : PELModuli.IntegralModel.PEL.Has.IntegralPELSpread P iota κ₀ N M.space M.universal B)
  [Smooth V.toOver.hom]
  {r : ℕ} (D : PELModuli.IntegralModel.Components.ComponentAlbaneseData V.toOver r) (e : (∐ D.S) ≅ V.toOver)

include hM hC hsplit hs hdegree hlabels hcop hpol hχ in
theorem exists_realization :
    ∃ C : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M.space,
      (Data.CM.data M V D e C χ).RealizesIsogenyQuotient := by
  have h (t : AbelianScheme.TateComparison.Local.IntegralType s) := ReferenceRealization.CM.Reference.exists_classified M hM κ₀ hC
    j aE hsplit hs hdegree labels hlabels hcop hpol Finite.DescentIntrinsic.CM.Intrinsic.input χ hχ t
  choose C f hf using h
  exact ⟨C, Realization.CM.realizes M V D e C χ f hf⟩

include hM hC hsplit hs hdegree hcop hpol in
theorem exists_paired_realization
    (a : (Fin s × Bool) ≃ Gal(E/ℚ))
    (ha : ∀ v b, a (v, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * a (v, b)) :
    ∃ C : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M.space,
      (Data.CM.data M V D e C (fun w => j.localCharacter aE (a w))).RealizesIsogenyQuotient :=
  exists_realization M hM κ₀ hC j aE hsplit hs hdegree (PairLabels.CM.labels a)
    (PairLabels.CM.swap a (fun σ => PELModuli.CMPoints.Arithmetic.rationalConjugation E * σ) ha)
    hcop hpol (fun w => j.localCharacter aE (a w)) (fun _ => rfl) V D e

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.Intrinsic.CM
