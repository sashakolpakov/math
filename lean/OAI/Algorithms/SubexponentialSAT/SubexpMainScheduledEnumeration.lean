import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainScheduledReconstruction
import OAI.Algorithms.SubexponentialSAT.SubexpMainPhysicalLayoutFields
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutEnumeration

namespace OAI.Algorithms

/-! The actual generated matrix banks enumerate the same scheduled,
table-bearing layout used for moment reconstruction. -/

namespace SubexponentialSAT.SubexpMainScheduledEnumeration

open SubexpMainProgram SubexpSetupProgram SubexpLayoutSpec
open SubexpPackingParameters SubexpMainScheduledLayout
open SubexpMainInvariant (Stored)
open SubexpLayoutPorts (Allocation)

local instance scheduledPrime (n : ℕ) : Fact (p n).Prime := ⟨p_prime n⟩

variable {cfg : Config} {er n B : ℕ} {hrBoot : 32 ≤ workRegs er} {hregs : 16 ≤ er}
variable {F : SAT.CNF (Fin n)} {alloc : Allocation (mainExtraStacks cfg)}
variable {a : MainState er (mainExtraStacks cfg)}
variable (boot : SubexpMainBoot.Run cfg hrBoot F) (initial : Stored cfg boot.setupOutput B a)
variable (ready : DyadicSchedule.Ready cfg.k cfg.T n)
variable {G : SubexpLeafData.Leaf n}
variable (input : SubexpMainLayoutInput.Ready alloc a n cfg.k cfg.T G)
variable [NeZero (r n)]
variable (actual : Run alloc hregs a G input ready)

noncomputable def numeric (t : Fin ((p n)^4 - 1)) :
    EnumerationData (actual.layout boot initial ready input) t :=
  SubexpMainLayoutEnumeration.enumeration
    (DyadicSchedule.parameters cfg.k cfg.T cfg.width_ge_two n (DyadicSchedule.ready_goodInput ready))
    rfl actual.result
    (SubexpMainLayoutPattern.bounded alloc a G input (by have := cfg.width_ge_two; omega))
    (by rw [SubexpMainParameterValues.sourceInputs_dimension alloc boot initial]
        exact SubexpMainDyadicReadiness.size cfg.k cfg.T cfg.width_ge_two ready)
    (SubexpMainDyadicReadiness.threshold cfg.k cfg.T cfg.width_ge_two ready)
    (SubexpMainDyadicReadiness.normalized_tail cfg.k cfg.T cfg.width_ge_two ready) t

noncomputable def physical (t : Fin ((p n)^4 - 1)) :
    EnumerationData (SubexpMainScheduledReconstruction.systemLayout boot initial ready input actual) t :=
  SubexpMainPhysicalLayoutFields.enumeration
    (SubexpMainLayoutInput.castLeaf input.variableCount.symm G)
    input.sparse.clause_sets_nodup input.ell_pos input.capacity input.dimension
    (actual.layout boot initial ready input) t (numeric boot initial ready input actual t)

noncomputable def images (t : Fin ((p n)^4 - 1)) :=
  SubexpMainLayoutEnumeration.images
    (DyadicSchedule.parameters cfg.k cfg.T cfg.width_ge_two n (DyadicSchedule.ready_goodInput ready))
    rfl actual.result t

theorem numeric_arrays (t : Fin ((p n)^4 - 1)) :
    (images ready input actual t).map (fun M => Subexp.MatrixImageEnumeration.bankRecords (p n) M.entries) =
      SubexpNodeBankBounds.outerBanks (numeric boot initial ready input actual t) ::
        SubexpNodeBankBounds.innerBanks (numeric boot initial ready input actual t) :=
  SubexpMainLayoutEnumeration.arrays_eq
    (DyadicSchedule.parameters cfg.k cfg.T cfg.width_ge_two n (DyadicSchedule.ready_goodInput ready))
    rfl actual.result
    (SubexpMainLayoutPattern.bounded alloc a G input (by have := cfg.width_ge_two; omega))
    (by rw [SubexpMainParameterValues.sourceInputs_dimension alloc boot initial]
        exact SubexpMainDyadicReadiness.size cfg.k cfg.T cfg.width_ge_two ready)
    (SubexpMainDyadicReadiness.threshold cfg.k cfg.T cfg.width_ge_two ready)
    (SubexpMainDyadicReadiness.normalized_tail cfg.k cfg.T cfg.width_ge_two ready) t

theorem physical_arrays (t : Fin ((p n)^4 - 1)) :
    (images ready input actual t).map (fun M => Subexp.MatrixImageEnumeration.bankRecords (p n) M.entries) =
      SubexpNodeBankBounds.outerBanks (physical boot initial ready input actual t) ::
        SubexpNodeBankBounds.innerBanks (physical boot initial ready input actual t) := by
  unfold physical
  rw [SubexpMainPhysicalLayoutFields.outerBanks, SubexpMainPhysicalLayoutFields.innerBanks]
  exact numeric_arrays boot initial ready input actual t

theorem bankBundle_eq (t : Fin ((p n)^4 - 1)) :
    ProgramEncoding.encodeRecords ((images ready input actual t).map SubexpNodeBankMap.bankList) =
      SubexpRawTemplate.bankBundle
        ((List.ofFn (physical boot initial ready input actual t).outerBase).map
          Subexp.RawTemplateRefinement.vectorBytes)
        (List.ofFn fun g =>
          (List.ofFn ((physical boot initial ready input actual t).increment g)).map
            Subexp.RawTemplateRefinement.vectorBytes) := by
  unfold physical
  rw [SubexpMainPhysicalLayoutFields.outerVectors]
  simp_rw [SubexpMainPhysicalLayoutFields.innerVectors]
  exact SubexpMainLayoutEnumeration.bankBundle_eq
    (DyadicSchedule.parameters cfg.k cfg.T cfg.width_ge_two n (DyadicSchedule.ready_goodInput ready))
    rfl actual.result
    (SubexpMainLayoutPattern.bounded alloc a G input (by have := cfg.width_ge_two; omega))
    (by rw [SubexpMainParameterValues.sourceInputs_dimension alloc boot initial]
        exact SubexpMainDyadicReadiness.size cfg.k cfg.T cfg.width_ge_two ready)
    (SubexpMainDyadicReadiness.threshold cfg.k cfg.T cfg.width_ge_two ready)
    (SubexpMainDyadicReadiness.normalized_tail cfg.k cfg.T cfg.width_ge_two ready) t

end SubexponentialSAT.SubexpMainScheduledEnumeration

end OAI.Algorithms
