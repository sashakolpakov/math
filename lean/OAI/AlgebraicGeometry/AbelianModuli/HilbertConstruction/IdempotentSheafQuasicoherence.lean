import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdempotentSheafSummands
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Kernels

/-! # Idempotent Sheaf Quasicoherence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdempotentSheafQuasicoherence

noncomputable section

/-! The actual idempotent summand of a quasicoherent sheaf is quasicoherent, by its explicit identification with the kernel of identity minus the projector. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}} {M : X.Modules}

def idempotentSheafKernelIso (p : End M) : IdempotentSheafSummands.idempotentSheafSummand p ≅ kernel ((1 : End M) - p) :=
  (Preadditive.isLimitKernelForkOfFork (equalizerIsEqualizer (𝟙 M) p)).conePointUniqueUpToIso
    (limit.isLimit (parallelPair ((1 : End M) - p) 0))

theorem idempotentSheafSummand_quasicoherent [M.IsQuasicoherent] (p : End M) :
    (IdempotentSheafSummands.idempotentSheafSummand p).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (idempotentSheafKernelIso p).symm (Quasicoherent.Kernels.module_quasicoherent_kernel ((1 : End M) - p))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdempotentSheafQuasicoherence
