import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.ParameterKernels
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.FineKernelData
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily

/-! # Fine Projectors -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.FineProjectors

noncomputable section

/-! Identify the original integral action with the action in the TateComparison
family. This equality transports the entire native kernel witness at once. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction

theorem integralType_exponentNat_antitone {s : ℕ} (t : AbelianScheme.TateComparison.Local.IntegralType s) (v : Fin s) :
    Antitone (t.exponentNat v) :=
  fun _ _ hij => Int.toNat_le_toNat (t.val.dominant v hij)

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
  (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N)

theorem fineFamily_action : AbelianScheme.TateComparison.PELAdapters.actionFromEnd (FineKernelData.fineFamily M).action = M.universal.action :=
  HeckeCycles.PELFamily.CM.Family.actionFromEnd_toEnd M.universal.action

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.FineProjectors
