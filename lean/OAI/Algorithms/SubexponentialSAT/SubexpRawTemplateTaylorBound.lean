import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTemplateCostBounds
import OAI.Algorithms.SubexponentialSAT.SubexpNodePacketRaw
import OAI.Algorithms.SubexponentialSAT.SubexpNodePacketInputs

namespace OAI.Algorithms

/-!
# Taylor-column bounds for the actual raw-template producer

Each physical factor packet has exactly degree+1 entries in every Taylor
column. The original-order color filter and both bank traversals preserve
that bound. The final theorem specializes to the actual node factor builder,
whose degree field is the supplied R; no TaylorBound premise remains.
-/

namespace SubexponentialSAT.SubexpRawTemplateTaylorBound

open SubexpSelectedConversions SubexpTemplateCostBounds
open Subexp.ConstructivePacking

variable {p D r Q Δ : ℕ} [Fact p.Prime]

theorem columns_length {labels arity degree : ℕ}
    (source : Prepared p 0) (target : Prepared p D)
    (theta : SubexpFactorPacketProvenance.Code p D)
    (input : SubexpFactorPacketProvenance.Input p D labels arity degree)
    (i : Fin arity) (column : List (List Bool))
    (hcolumn : column ∈ SubexpFactorPacketProvenance.columns source target theta input i) :
    column.length = degree + 1 := by
  rw [SubexpFactorPacketProvenance.columns_eq] at hcolumn
  obtain ⟨w, rfl⟩ := List.mem_ofFn.mp hcolumn
  simp only [List.length_ofFn]

theorem blueprintRows_factorBound {labels arity degree : ℕ}
    (source : Prepared p 0) (target : Prepared p D)
    (theta : SubexpFactorPacketProvenance.Code p D)
    (input : SubexpFactorPacketProvenance.Input p D labels arity degree)
    (R : ℕ) (hdegree : degree ≤ R) :
    FactorBound (R + 1) (SubexpFactorPacketProvenance.blueprintRows source target theta input) := by
  intro row hrow
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp hrow
  intro coordinate hcoordinate
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hcoordinate
  intro column hcolumn
  change column ∈ SubexpFactorPacketProvenance.columns source target theta input i at hcolumn
  rw [columns_length source target theta input i column hcolumn]
  omega

theorem packet_factorBound {F : Type*}
    (source : Prepared p 0) (target : Prepared p D)
    (theta : SubexpFactorPacketProvenance.Code p D)
    (factor : F → SubexpFactorPacketCorrectness.FactorInput p D)
    (R : ℕ) (f : F) (hdegree : (factor f).degree ≤ R) :
    FactorBound (R + 1) (SubexpNodePacketRaw.packet source target theta factor f) :=
  blueprintRows_factorBound source target theta (factor f).data R hdegree

omit [Fact (Nat.Prime p)] in
/-- Filtering preserves packet bounds and retains every duplicate occurrence. -/
theorem raw_blocks_bound {F : Type*}
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ)) (node : Fin Q)
    (order : List F) (words : F → MulticolorTypes.Word r Q)
    (packets : F → SubexpTemplateFactors.Factor p D)
    (bases : List (Fin D → ZMod p)) (increments : Fin r → List (Fin D → ZMod p))
    (q : ℕ) (hpackets : ∀ f ∈ order, FactorBound q (packets f)) :
    TaylorBound q
      (Subexp.RawTemplateRefinement.blocks P node order words packets bases increments) := by
  intro block hblock
  obtain ⟨base, _, rfl⟩ := List.mem_map.mp hblock
  intro group hgroup
  obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hgroup
  intro term hterm
  obtain ⟨increment, _, rfl⟩ := List.mem_map.mp hterm
  intro packet hpacket
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hpacket
  exact hpackets f (List.mem_filter.mp hf).1

/-- Actual factor packets, actual color filtering, and actual bank order. -/
theorem blocks_taylorBound {F : Type*}
    (source : Prepared p 0) (target : Prepared p D)
    (theta : SubexpFactorPacketProvenance.Code p D)
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ)) (node : Fin Q)
    (order : List F) (words : F → MulticolorTypes.Word r Q)
    (factor : F → SubexpFactorPacketCorrectness.FactorInput p D)
    (bases : List (Fin D → ZMod p)) (increments : Fin r → List (Fin D → ZMod p))
    (R : ℕ) (hdegree : ∀ f ∈ order, (factor f).degree ≤ R) :
    TaylorBound (R + 1)
      (Subexp.RawTemplateRefinement.blocks P node order words
        (SubexpNodePacketRaw.packet source target theta factor) bases increments) := by
  apply raw_blocks_bound
  intro f hf
  exact packet_factorBound source target theta factor R f (hdegree f hf)

/-- The node worker fixes the packet degree to R by construction. -/
theorem node_blocks_taylorBound
    (source : Prepared p 0) (target : Prepared p D)
    (theta : SubexpFactorPacketProvenance.Code p D)
    (R : ℕ) (sourceWidth : List Bool)
    (hw : sourceWidth.length = SubexpLiftRing.baseWidth p 1)
    (cache : List (List (SubexpFactorPacketProvenance.Code p D)))
    (zero one : SubexpFactorPacketProvenance.Code p D)
    (expr : ℕ → ℕ → ℕ → SubexpTaylorRowCorrectness.RowExpr p)
    (scopes : List (List ℕ)) (tables : List (List Bool))
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ)) (node : Fin Q)
    (words : Fin scopes.length → MulticolorTypes.Word r Q)
    (bases : List (Fin D → ZMod p)) (increments : Fin r → List (Fin D → ZMod p)) :
    TaylorBound (R + 1)
      (Subexp.RawTemplateRefinement.blocks P node (List.finRange scopes.length) words
        (SubexpNodePacketRaw.packet source target theta
          (SubexpNodePacketInputs.factor source target theta R sourceWidth hw
            cache zero one expr scopes tables)) bases increments) := by
  apply blocks_taylorBound
  intro f hf
  exact Nat.le_refl R

end SubexponentialSAT.SubexpRawTemplateTaylorBound

end OAI.Algorithms
