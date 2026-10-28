import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Presentation
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Cohomology

/-! # Comparison Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ComparisonAction.CM

noncomputable section

/-! Apply the proved endomorphism-presentation bridge to the very same
Albanese and rational cohomology operators supplied by TateComparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Presentation.CM.Hecke
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison.CM

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
  (hcop : Nat.Coprime q D.denominator)

theorem integral_betti_agrees (a : D.EndK) :
    (AlbaneseModel.CM.comparisonModel D hg j hcop).bettiPullback D.complexEmbedding
      (Presentation.CM.Hecke.extendingEndomorphism (AlbaneseModel.CM.comparisonModel D hg j hcop)
        (EndomorphismComparison.CM.integralEquiv (AlbaneseModel.CM.comparisonModel D hg j hcop).variety.scheme a)) =
      D.pullbackH1Integral a := rfl

/-- TateComparison's actual clearing equations imply a GeometricComparison realization on the
constructed model, with exactly TateComparison's original Betti action. -/
theorem native_hecke_realization
    {H : Type} [CommRing H] [Algebra ℚ H]
    (ρ : H →ₐ[ℚ] D.EndQ) (T : H →ₐ[ℚ] Module.End ℚ D.H1)
    (hTateComparison : ∀ h, D.IsRationalH1Pullback (ρ h) (T h)) :
    ∃ R : (AlbaneseModel.CM.comparisonModel D hg j hcop).HeckeRealization H,
      R.action = (EndomorphismComparison.CM.rationalEquiv (AlbaneseModel.CM.comparisonModel D hg j hcop).variety.scheme).toAlgHom.comp ρ ∧
      (AlbaneseModel.CM.comparisonModel D hg j hcop).bettiHecke D.complexEmbedding R = T := by
  apply Presentation.CM.Hecke.exists_hecke_realization_with_betti (AlbaneseModel.CM.comparisonModel D hg j hcop) ρ
    (fun h => by
      obtain ⟨n, hn, a, ha⟩ := (hTateComparison h).1
      exact ⟨n, hn, a, ha⟩) D.complexEmbedding T
  intro h n hn a ha
  exact ((hTateComparison h).2 n hn a ha).trans (integral_betti_agrees D hg j hcop a).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ComparisonAction.CM
