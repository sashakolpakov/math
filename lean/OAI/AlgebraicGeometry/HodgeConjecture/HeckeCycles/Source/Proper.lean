import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMapCompatibility

/-! # Proper -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Proper.CM

noncomputable section

/-! Properness and smoothness of the actual source over the q-adic
integers follow by base change from the full IntegralModel geometry. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMapCompatibility.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
  (hcop : Nat.Coprime q D.denominator)

theorem integralSource_proper : IsProper (AlbaneseMapCompatibility.CM.integralSource D hg j hcop).hom := by
  let : IsProper D.model.space.hom := hg.proper
  exact inferInstanceAs
    (IsProper (pullback.snd D.model.space.hom (QadicModelMap.CM.integralBase j D.denominator hcop)))

theorem integralSource_smooth : Smooth (AlbaneseMapCompatibility.CM.integralSource D hg j hcop).hom := by
  let : Smooth D.model.space.hom := hg.smooth
  exact inferInstanceAs
    (Smooth (pullback.snd D.model.space.hom (QadicModelMap.CM.integralBase j D.denominator hcop)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Proper.CM
