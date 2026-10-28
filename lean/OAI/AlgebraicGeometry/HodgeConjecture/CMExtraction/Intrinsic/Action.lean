import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonPointEquation
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Interface

/-! # Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Action

noncomputable section

/-! TateComparison's full point-push conclusion is the original raw-action predicate. -/

open OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonPointEquation.CM.Raw

theorem native_c47_raw_action
    {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AbelianScheme.CentralAction.Interface.Construction.ActionData D) (hA : AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A)
    (t : AbelianScheme.TateComparison.Local.IntegralType s) : HeckeCycles.TateComparisonPointEquation.CM.Raw.RawAction D hg t (A.TAlb t) :=
  hA.pointPush t

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Action
