import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalEnumeration

namespace OAI.Algorithms

/-!
# Executable carriers for the local enumerated fixed spaces

The submodule values passed to executable blockwise data constructors use
decidable zero extension. The mathematical fixed-space carrier is related by
equality, used only to transport the finished record.
-/

namespace SubexponentialSAT.Subexp.ComputedLocalEnumeration

open SubexponentialSAT.MulticolorTypes
open LocalEnumeration BlockwiseEnumeration
open _root_.OAI.Algorithms.SubexponentialSAT.Subexp.SubspaceDimension
open BlockSearch

variable {p r Q Δ : ℕ} [Fact p.Prime]

/-- The local space as a computable submodule value. -/
def canonicalSpace (t : Fin Q) (g : Fin r) (R : ℕ) (coeff : ℕ → ZMod p) :
    Submodule (ZMod p) (UniversalType r Q Δ → ZMod p) :=
  computedSupportedSpace (side t g) (joint t g) (joint_subset_side t g)
    (fun i => (ElementaryMatrix.jointMatrixDP i t g R coeff).mulVecLin)

theorem canonicalSpace_eq (t : Fin Q) (g : Fin r) (R : ℕ) (coeff : ℕ → ZMod p) :
    canonicalSpace (Δ := Δ) t g R coeff = universalFixedSpace t g
      (fun i => (MatrixSupport.jointMatrix i t g R coeff).mulVecLin) := by
  unfold canonicalSpace
  rw [computedSupportedSpace_eq]
  change universalFixedSpace t g _ = _
  apply congrArg (fun M => universalFixedSpace t g M)
  funext i
  exact congrArg Matrix.mulVecLin (ElementaryMatrix.jointMatrixDP_eq i t g R coeff)

/-- Actual exhaustive side searches, with a computable target family suitable
for subsequent blockwise execution. -/
noncomputable def executableLocalData (t : Fin Q) (R : ℕ) (coeff : ℕ → ZMod p) :
    LocalData (ZMod p) (UniversalType r Q Δ) r
      (fun g => canonicalSpace t g R coeff) :=
  cast (congrArg (fun W => LocalData (ZMod p) (UniversalType r Q Δ) r W)
    (funext (fun g => canonicalSpace_eq t g R coeff)).symm)
    (canonicalLocalData t R coeff)

/-- A successful encoded search can supply its own side pairs. Its search
order need not match the exhaustive Lean implementation. -/
noncomputable def executableLocalDataForPairs (t : Fin Q) (R : ℕ) (coeff : ℕ → ZMod p)
    (pairs : (g : Fin r) →
      Candidate (ZMod p) (FiberEnumeration.sideList (Δ := Δ) t g).length ×
        Candidate (ZMod p) (FiberEnumeration.sideList (Δ := Δ) t g).length)
    (hpairs : ∀ g, GoodPair (canonicalConstraintMatrix (Δ := Δ) t g R coeff) (pairs g)) :
    LocalData (ZMod p) (UniversalType r Q Δ) r
      (fun g => canonicalSpace t g R coeff) :=
  cast (congrArg (fun W => LocalData (ZMod p) (UniversalType r Q Δ) r W)
    (funext (fun g => canonicalSpace_eq t g R coeff)).symm)
    (universalLocalDataForPairs t R coeff pairs hpairs)

end SubexponentialSAT.Subexp.ComputedLocalEnumeration

end OAI.Algorithms
