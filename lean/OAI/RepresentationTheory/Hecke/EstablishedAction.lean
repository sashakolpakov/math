import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Intrinsic
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Tate
import OAI.RepresentationTheory.Theta.Geometric.TateComparison

/-! # Established Action -/

namespace OAI.RepresentationTheory.Hecke.EstablishedAction.CentralConstraintIntrinsic

theorem proved_action_output
    {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s) :
    Theta.Geometric.TateComparison.TateComparisonOutput D hg hq hIsogenyQuotient :=
  (AlgebraicGeometry.AbelianScheme.CentralAction.Tate.Construction.c47_input_equivalence D hg hq hIsogenyQuotient).mpr
    ⟨AlgebraicGeometry.AbelianScheme.CentralAction.Intrinsic.Construction.nativeTateComparisonAction D hg hq hIsogenyQuotient hdegree hs,
      AlgebraicGeometry.AbelianScheme.CentralAction.Intrinsic.Construction.nativeTateComparisonAction_spec D hg hq hIsogenyQuotient hdegree hs⟩

end OAI.RepresentationTheory.Hecke.EstablishedAction.CentralConstraintIntrinsic
