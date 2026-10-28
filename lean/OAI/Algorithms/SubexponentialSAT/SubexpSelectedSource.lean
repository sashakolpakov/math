import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSelectedConversions
import OAI.Algorithms.SubexponentialSAT.SubexpCountSource

namespace OAI.Algorithms

/-!
# Selected counting from source rows with concrete word conversions

All three conversion fields of the generic selected input are filled by the
actual word operations. The caller supplies only the remaining finite source
data and their local layout identities. Taylor coefficients are constructed
by the represented compiler, rather than included as input certificates.

These are value-level representation and counting theorems. They do not
supply a complete primitive-machine execution or its time bound.
-/

noncomputable section

namespace SubexponentialSAT.SubexpSelectedSource

open SubexpLayoutSpec SubexpSelectedConversions

variable {D p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {F : Type*} [Fintype F] [DecidableEq F]
  (S : Factor.System (Fin D) F (ZMod p))
  {c : Parameters p k Δ r tau}
  (L : Layout (E := SubexpActualRing.E p) S.toPattern c)
  (source : Prepared p 0) (target : Prepared p D)
  (input : SubexpCountSource.SourceInput S L source.residueRing target.ring)

/-- No conversion law or Taylor-array certificate is a caller argument. -/
def toSelectedInput :
    SubexpCountExecution.SelectedInput S L source.residueRing target.ring :=
  SubexpCountSource.SourceInput.toSelectedInput S L source.residueRing target.ring input
    embedCode (betaLift source D) (weightCode source D)
    (embedCode_decode source) (betaLift_decode source target) (weightCode_decode source target)

theorem run_coeff_zero (hD : 0 < D) :
    (PolynomialAlgorithm.denote
      ((SubexpCountExecution.runSelected S L source.residueRing target.ring
        (toSelectedInput S L source target input)).1.map target.ring.decode)).coeff 0 =
      (Factor.count S : SubexpActualRing.Ring p (D + 1)) :=
  SubexpCountExecution.runSelected_coeff_zero S L source.residueRing target.ring _ hD

/-- The concrete conversion specialization recovers the full natural count.
Only the finite source-layout identities and positive dimension remain. -/
theorem run_decodeCount (hD : 0 < D) :
    SubexpActualRing.decodeCount p (D + 1) (Nat.succ_pos D)
      ((PolynomialAlgorithm.denote
        ((SubexpCountExecution.runSelected S L source.residueRing target.ring
          (toSelectedInput S L source target input)).1.map target.ring.decode)).coeff 0) =
      Factor.count S :=
  SubexpCountExecution.runSelected_decodeCount S L source.residueRing target.ring _ hD

/-- The same endpoint with both sets of arithmetic caches constructed by
the binary initializer. No prepared-cache certificate is supplied by the
caller; only the prime word's value and width are identified. -/
theorem initialized_run_decodeCount (primeBits : List Bool)
    (hvalue : BinaryArithmetic.toNat primeBits = p)
    (hwidth : primeBits.length = Nat.log 2 p + 1)
    (data : SubexpCountSource.SourceInput S L
      (initializeSelected p 0 primeBits hvalue hwidth).residueRing
      (initializeSelected p D primeBits hvalue hwidth).ring)
    (hD : 0 < D) :
    let source := initializeSelected p 0 primeBits hvalue hwidth
    let target := initializeSelected p D primeBits hvalue hwidth
    SubexpActualRing.decodeCount p (D + 1) (Nat.succ_pos D)
      ((PolynomialAlgorithm.denote
        ((SubexpCountExecution.runSelected S L source.residueRing target.ring
          (toSelectedInput S L source target data)).1.map target.ring.decode)).coeff 0) =
      Factor.count S :=
  run_decodeCount S L (initializeSelected p 0 primeBits hvalue hwidth)
    (initializeSelected p D primeBits hvalue hwidth) data hD

end SubexponentialSAT.SubexpSelectedSource

end

end OAI.Algorithms
