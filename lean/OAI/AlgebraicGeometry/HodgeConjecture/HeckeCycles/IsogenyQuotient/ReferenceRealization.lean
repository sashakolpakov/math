import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.Fine
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.ParameterClassification
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IntegralHecke

/-! # Reference Realization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.ReferenceRealization.CM.Reference

noncomputable section

/-! The full native IsogenyQuotient theorem gives actual original fine-model
correspondences whose independent chosen kernels classify every test.
All quotient and raw-Hecke clauses remain in the theorem being applied. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators
open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IntegralHecke.Construction

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
  (hFiniteDescent : AbelianScheme.IsogenyQuotient.IsogenyComplement.Construction.FiniteDescentInput.{0})
  (χ : Fin s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q])
  (hχ : ∀ v, χ (v, false) = j.localCharacter aE (labels (.inl v)))

include hM hC hsplit hs hdegree hlabels hcop hpol hFiniteDescent hχ in
theorem exists_classified (t : AbelianScheme.TateComparison.Local.IntegralType s) :
    ∃ C : AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M.space,
      ∃ f : CMExtraction.IsogenyQuotient.FineKernelData.UniversalIsogeny (q := q) M C t, CMExtraction.IsogenyQuotient.FineKernelData.ClassifiesChosenKernels M C t χ f := by
  have hfull := AbelianScheme.IsogenyQuotient.IntegralHecke.Construction.integral_hecke_family_exists M hM κ₀ hC j aE hsplit hs hdegree t.multiplierNat
    labels hlabels t.exponentNat t.exponentNat_le (FineProjectors.CM.exponentNat_antitone t)
    hcop hpol hFiniteDescent
  obtain ⟨Q, hQf, hQe, repr, _e, _hsource, _hfinite, _hetale, model, f, hker, _hisotropic, _hraw⟩ := hfull
  let C := Fine.CM.Isogeny.correspondence M Q hQf hQe f
  let f' := Fine.CM.Isogeny.isogeny M hM κ₀ hC Q f
  let hA := AbelianScheme.IsogenyQuotient.FinePELUniversalFunctions.Construction.finePEL_universal_hasUniversalGlobalFunctions M hM κ₀ hC
  let b := AbelianScheme.IsogenyQuotient.UniversalFunction.PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing M.universal.polarized.abelian
    M.universal.polarized.dual M.universal.polarized.polarization
    (AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source M.universal.polarized.polarization.isogeny.hom hA)
    (q ^ t.multiplierNat) (pow_pos (Fact.out : q.Prime).pos t.multiplierNat)
  let ep := AbelianScheme.IsogenyQuotient.CM.PointsPerfectKernel.Construction.l45SourceBlockPairing j aE hsplit M.universal.polarized.abelian M.universal.action
    t.multiplierNat s labels b
  refine ⟨C, f', ?_⟩
  exact ParameterClassification.CM.classifies M j aE hsplit t labels M.universal.action
    Q repr ep model f.target hQf hQe f' hker (FineProjectors.CM.action M) χ hχ

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.ReferenceRealization.CM.Reference
