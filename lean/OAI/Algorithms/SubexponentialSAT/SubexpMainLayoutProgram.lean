import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutPrefixWorkspace
import OAI.Algorithms.SubexponentialSAT.SubexpMainCoefficients
import OAI.Algorithms.SubexponentialSAT.SubexpMainScalarAlphabet
import OAI.Algorithms.SubexponentialSAT.SubexpMainScalarFrameWidth
import OAI.Algorithms.SubexponentialSAT.SubexpMainPackingState
import OAI.Algorithms.SubexponentialSAT.SubexpMainLocalBasisCode
import OAI.Algorithms.SubexponentialSAT.SubexpMainCacheSetup
import OAI.Algorithms.SubexponentialSAT.SubexpMainLagrangeCacheControl
import OAI.Algorithms.SubexponentialSAT.SubexpMainRowsProgram

namespace OAI.Algorithms

/-! The fixed static-layout controller. Every phase below is an actual
finite program. Saved data occupy the Main layout bank; each subsequent
phase reads its physical outputs through its proved port map.

The execution and semantic refinement are added once the final native
local-basis, Lagrange, and row producers publish their proofs. This file
does not introduce a runtime semantic callback or a chosen-layout oracle.
-/

namespace SubexponentialSAT.SubexpMainLayoutProgram

open SubexpMainProgram
open SubexpLayoutPorts (Allocation)

/-- Construct the factor streams and assignment, then the scalar alphabet,
coefficient vector, packing and local basis records. All of these run
before the source-cache bank is initialized. -/
noncomputable def choices (er : ℕ) (hr : 16 ≤ er) {es : ℕ}
    (alloc : Allocation es) : Procedure er es :=
  SubexpProcedureCompose.sequence (SubexpMainLayoutPrefix.procedure er alloc)
    (SubexpProcedureCompose.sequence (SubexpMainCoefficients.procedure er alloc)
      (SubexpProcedureCompose.sequence (SubexpMainScalarAlphabet.procedure er alloc)
        (SubexpProcedureCompose.sequence (SubexpMainScalarFrameWidth.procedure er alloc)
          (SubexpProcedureCompose.sequence (SubexpMainPacking.procedure er alloc)
            (SubexpMainLocalBasis.procedure er hr alloc)))))

/-- Build both prepared-ring caches and the complete Lagrange master, then
execute source-row preparation and the complete dense-row traversal. -/
noncomputable def rows (er : ℕ) (hr : 16 ≤ er) {es : ℕ}
    (alloc : Allocation es) : Procedure er es :=
  SubexpProcedureCompose.sequence (SubexpMainCacheSetup.procedure er alloc)
    (SubexpProcedureCompose.sequence (SubexpMainLagrangeCache.procedure er alloc)
      (SubexpMainRows.procedure er hr alloc))

noncomputable def procedure (er : ℕ) (hr : 16 ≤ er) {es : ℕ}
    (alloc : Allocation es) : Procedure er es :=
  SubexpProcedureCompose.sequence (choices er hr alloc) (rows er hr alloc)

noncomputable def program (er : ℕ) (hr : 16 ≤ er) {es : ℕ} (alloc : Allocation es) :=
  (procedure er hr alloc).program

end SubexponentialSAT.SubexpMainLayoutProgram

end OAI.Algorithms
