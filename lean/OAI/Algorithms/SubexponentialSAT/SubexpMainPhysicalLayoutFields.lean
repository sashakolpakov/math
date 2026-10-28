import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainPhysicalSystem
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBankBounds

namespace OAI.Algorithms

/-! Pattern equality changes only the dependent type of a layout and its
enumeration. The actual nodes, spaces, vectors and serialized bank order are
preserved. No fresh basis or enumeration is selected. -/

namespace SubexponentialSAT.SubexpMainPhysicalLayoutFields

open SubexpLayoutSpec

namespace PatternTransport

variable {D p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {F E : Type*} [Fintype F] [Field E] [Algebra (ZMod p) E]
  {P P' : Factor.Pattern (Fin D) F} {c : Parameters p k Δ r tau}

def layout (h : P = P') (L : Layout (E := E) P c) : Layout (E := E) P' c := h ▸ L

theorem node (h : P = P') (L : Layout (E := E) P c) (t : Fin c.Q) :
    (layout h L).node t = L.node t := by cases h; rfl

theorem support (h : P = P') (L : Layout (E := E) P c) :
    (layout h L).support = L.support := by cases h; rfl

theorem subspaces (h : P = P') (L : Layout (E := E) P c) :
    (layout h L).K = L.K := by cases h; rfl

def enumeration (h : P = P') (L : Layout (E := E) P c) (t : Fin c.Q)
    (e : EnumerationData L t) : EnumerationData (layout h L) t := by
  cases h
  exact e

theorem outerVectors (h : P = P') (L : Layout (E := E) P c) (t : Fin c.Q)
    (e : EnumerationData L t) :
    List.ofFn (enumeration h L t e).outerBase = List.ofFn e.outerBase := by cases h; rfl

theorem innerVectors (h : P = P') (L : Layout (E := E) P c) (t : Fin c.Q)
    (e : EnumerationData L t) (g : Fin r) :
    List.ofFn ((enumeration h L t e).increment g) = List.ofFn (e.increment g) := by cases h; rfl

theorem outerBanks (h : P = P') (L : Layout (E := E) P c) (t : Fin c.Q)
    (e : EnumerationData L t) :
    SubexpNodeBankBounds.outerBanks (enumeration h L t e) =
      SubexpNodeBankBounds.outerBanks e := by cases h; rfl

theorem innerBanks (h : P = P') (L : Layout (E := E) P c) (t : Fin c.Q)
    (e : EnumerationData L t) :
    SubexpNodeBankBounds.innerBanks (enumeration h L t e) =
      SubexpNodeBankBounds.innerBanks e := by cases h; rfl

theorem bankBundle (h : P = P') (L : Layout (E := E) P c) (t : Fin c.Q)
    (e : EnumerationData L t) :
    SubexpNodeBankBounds.bankBundle (enumeration h L t e) =
      SubexpNodeBankBounds.bankBundle e := by cases h; rfl

theorem iterationCount (h : P = P') (L : Layout (E := E) P c) (t : Fin c.Q)
    (e : EnumerationData L t) :
    (enumeration h L t e).iterationCount = e.iterationCount := by cases h; rfl

end PatternTransport

variable {n ell D p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
variable (G : SubexpLeafData.Leaf n) (hG : (G.map ExecCNF.clauseSet).Nodup)
variable (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (hD : D = ChunkPartition.count n ell)
variable {c : Parameters p k Δ r tau}
variable (L : Layout (E := SubexpActualRing.E p)
  (Subexp.IncidencePlanSpec.pattern D (SubexpLeafScopeOrder.rawScopes G hG hell)) c)

theorem node (t : Fin c.Q) :
    (SubexpMainPhysicalSystem.layout G hG hell hcap hD L).node t = L.node t :=
  PatternTransport.node (SubexpMainPhysicalSystem.system_toPattern G hG hell hcap hD).symm L t

theorem support :
    (SubexpMainPhysicalSystem.layout G hG hell hcap hD L).support = L.support :=
  PatternTransport.support (SubexpMainPhysicalSystem.system_toPattern G hG hell hcap hD).symm L

theorem subspaces :
    (SubexpMainPhysicalSystem.layout G hG hell hcap hD L).K = L.K :=
  PatternTransport.subspaces (SubexpMainPhysicalSystem.system_toPattern G hG hell hcap hD).symm L

noncomputable def enumeration (t : Fin c.Q) (e : EnumerationData L t) :
    EnumerationData (SubexpMainPhysicalSystem.layout G hG hell hcap hD L) t :=
  PatternTransport.enumeration (SubexpMainPhysicalSystem.system_toPattern G hG hell hcap hD).symm L t e

theorem outerVectors (t : Fin c.Q) (e : EnumerationData L t) :
    List.ofFn (enumeration G hG hell hcap hD L t e).outerBase = List.ofFn e.outerBase :=
  PatternTransport.outerVectors (SubexpMainPhysicalSystem.system_toPattern G hG hell hcap hD).symm L t e

theorem innerVectors (t : Fin c.Q) (e : EnumerationData L t) (g : Fin r) :
    List.ofFn ((enumeration G hG hell hcap hD L t e).increment g) = List.ofFn (e.increment g) :=
  PatternTransport.innerVectors (SubexpMainPhysicalSystem.system_toPattern G hG hell hcap hD).symm L t e g

theorem outerBanks (t : Fin c.Q) (e : EnumerationData L t) :
    SubexpNodeBankBounds.outerBanks (enumeration G hG hell hcap hD L t e) =
      SubexpNodeBankBounds.outerBanks e :=
  PatternTransport.outerBanks (SubexpMainPhysicalSystem.system_toPattern G hG hell hcap hD).symm L t e

theorem innerBanks (t : Fin c.Q) (e : EnumerationData L t) :
    SubexpNodeBankBounds.innerBanks (enumeration G hG hell hcap hD L t e) =
      SubexpNodeBankBounds.innerBanks e :=
  PatternTransport.innerBanks (SubexpMainPhysicalSystem.system_toPattern G hG hell hcap hD).symm L t e

theorem bankBundle (t : Fin c.Q) (e : EnumerationData L t) :
    SubexpNodeBankBounds.bankBundle (enumeration G hG hell hcap hD L t e) =
      SubexpNodeBankBounds.bankBundle e :=
  PatternTransport.bankBundle (SubexpMainPhysicalSystem.system_toPattern G hG hell hcap hD).symm L t e

theorem iterationCount (t : Fin c.Q) (e : EnumerationData L t) :
    (enumeration G hG hell hcap hD L t e).iterationCount = e.iterationCount :=
  PatternTransport.iterationCount (SubexpMainPhysicalSystem.system_toPattern G hG hell hcap hD).symm L t e

end SubexponentialSAT.SubexpMainPhysicalLayoutFields

end OAI.Algorithms
