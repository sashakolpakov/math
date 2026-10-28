import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseRowProducer
import OAI.Algorithms.SubexponentialSAT.SubexpGlobalRowSemantics

namespace OAI.Algorithms

/-! The actual nested row-table payload at a valid factor incidence.
The slot is computed from the emitted outer scope list. This adapter does
not assume equality of a produced row to a requested polynomial. -/

namespace SubexponentialSAT.SubexpDenseRowSemantics

open SubexpLiftRing SubexpQuarticRing SubexpSelectedConversions
open SubexpRepresentedRows SubexpRowInterpolation SubexpTaylorExecution
open Subexp.ConstructivePacking MulticolorTypes

variable {p r Q Δ D : ℕ} [Fact p.Prime]
variable (source : Prepared p 0) (xs : List (ZMod p))
variable (inverse negative : Fin Q → List Bool)
variable (difference : Fin Q → Fin Q → List Bool)
variable (P : PackingData (Fin D) (UniversalType r Q Δ))
variable (scopes : List (List ℕ))
variable (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ)

/-- The concrete coefficient list at the row-table traversal's indices. -/
def rowCoefficients (μ : ℕ) (e : Fin scopes.length) (v : Fin D)
    (hv : v.val ∈ scopes.get e) (w : Fin D) : List (Quad (Word (baseWidth p μ))) :=
  SubexpGlobalRowSemantics.coefficientsAt source xs inverse negative difference μ P
    (SubexpDenseRowProducer.slot scopes hd e v hv) v w

/-- The complete forward row payload, without any permutation or padding
assumption, is exactly the encoding of these generated coefficients. -/
theorem render_eq_encode (μ : ℕ) (e : Fin scopes.length) (v : Fin D)
    (hv : v.val ∈ scopes.get e) (w : Fin D) :
    SubexpDenseRowProducer.render μ source xs inverse negative difference P scopes hd
      e.val v.val w.val =
      SubexpCoefficientLiftArray.encodeArray
        (rowCoefficients source xs inverse negative difference P scopes hd μ e v hv w) := by
  rw [SubexpDenseRowProducer.render_at μ source xs inverse negative difference P scopes hd
    e.val v.val w.val e.isLt v.isLt w.isLt hv]
  exact SubexpGlobalRowSemantics.outputAt_forward source xs inverse negative difference μ P
    (SubexpDenseRowProducer.slot scopes hd e v hv) v w

variable (cache : NodeCache (SubexpSymbolicCost.QuarticCode p 0) Q)
variable {node : Fin Q → SubexpActualRing.E p} (units : NodeUnits node)
variable (hnode : ∀ j, source.residueRing.decode (cache.node j) = node j)
variable (hinv : ∀ j, source.residueRing.decode (cache.inverse j) = units.nodeInverse j)
variable (hdiff : ∀ j k,
  source.residueRing.decode (cache.difference j k) = units.differenceInverse j k)
variable (hinverse : ∀ j, SubexpRawRow.scalarDecode source (inverse j) =
  source.residueRing.decode (cache.inverse j))
variable (hnegative : ∀ j, SubexpRawRow.scalarDecode source (negative j) =
  source.residueRing.decode ((source.residueRing.negRun (cache.node j)).1))
variable (hdifference : ∀ j k, SubexpRawRow.scalarDecode source (difference j k) =
  source.residueRing.decode (cache.difference j k))

include hnode hinv hdiff hinverse hnegative hdifference in
/-- At every actual factor/scope/coordinate index, the generated payload
denotes the represented factor-source row with its actual incidence slot. -/
theorem rowCoefficients_denote (A R : ℕ) (hlength : xs.length = R)
    (hcheck : ∀ d : Fin R,
      Subexp.CoefficientDynamics.evaluate xs (A + d.val) = (-1 : ZMod p) ^ (A + d.val))
    {N : ℕ} (target : Prepared p N)
    (e : Fin scopes.length) (v : Fin D) (hv : v.val ∈ scopes.get e) (w : Fin D) :
    PolynomialAlgorithm.denote
      ((rowCoefficients source xs inverse negative difference P scopes hd (N + 1) e v hv w).map
        target.ring.decode) =
      (mapCode target.ring.decode
        (liftCode source.program target.program (betaLift source N) R
          (Subexp.ComputedRowSource.globalCode source.program cache embedCode R
            (Subexp.CoefficientSearch.coefficientsNat p A R) P
            (SubexpDenseRowProducer.slot scopes hd e v hv) v w))).denote := by
  exact SubexpGlobalRowSemantics.coefficientsAt_denote_liftCode source xs inverse negative difference
    cache units hnode hinv hdiff hinverse hnegative hdifference A R hlength hcheck target P
    (SubexpDenseRowProducer.slot scopes hd e v hv) v w

end SubexponentialSAT.SubexpDenseRowSemantics

end OAI.Algorithms
