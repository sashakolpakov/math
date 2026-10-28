import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainPhysicalLayoutFields

namespace OAI.Algorithms

/-! Row and color preservation across the proved equality between the
numeric scope pattern and its table-bearing physical factor system. -/

namespace SubexponentialSAT.SubexpMainPhysicalLayoutRows

open SubexpLayoutSpec

namespace PatternTransport

variable {D p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {F E : Type*} [Fintype F] [Field E] [Algebra (ZMod p) E]
  {P P' : Factor.Pattern (Fin D) F} {c : Parameters p k Δ r tau}

def scopeBack (h : P = P') (e : F) (v : {v // v ∈ P'.scope e}) :
    {v // v ∈ P.scope e} := by
  cases h
  exact v

omit [Fintype F] in
theorem scopeBack_val (h : P = P') (e : F) (v : {v // v ∈ P'.scope e}) :
    (scopeBack h e v).val = v.val := by cases h; rfl

theorem color (h : P = P') (L : Layout (E := E) P c) :
    (SubexpMainPhysicalLayoutFields.PatternTransport.layout h L).color = L.color := by
  cases h
  rfl

theorem row (h : P = P') (L : Layout (E := E) P c)
    (e : F) (v : {v // v ∈ P'.scope e}) (w : Fin D) :
    (SubexpMainPhysicalLayoutFields.PatternTransport.layout h L).row e v w =
      L.row e (scopeBack h e v) w := by
  cases h
  rfl

theorem row_at (h : P = P') (L : Layout (E := E) P c)
    (e : F) (v w : Fin D) (hv : v ∈ P.scope e) (hv' : v ∈ P'.scope e) :
    (SubexpMainPhysicalLayoutFields.PatternTransport.layout h L).row e ⟨v, hv'⟩ w =
      L.row e ⟨v, hv⟩ w := by
  cases h
  rfl

end PatternTransport

variable {n ell D p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
variable (G : SubexpLeafData.Leaf n) (hG : (G.map ExecCNF.clauseSet).Nodup)
variable (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (hD : D = ChunkPartition.count n ell)
variable {c : Parameters p k Δ r tau}
variable (L : Layout (E := SubexpActualRing.E p)
  (Subexp.IncidencePlanSpec.pattern D (SubexpLeafScopeOrder.rawScopes G hG hell)) c)

noncomputable def scopeBack (e : Fin (SubexpLeafScopeOrder.rawScopes G hG hell).length)
    (v : {v // v ∈ (SubexpMainPhysicalSystem.system G hG hell hcap hD).scope e}) :
    {v // v ∈ (Subexp.IncidencePlanSpec.pattern D
      (SubexpLeafScopeOrder.rawScopes G hG hell)).scope e} :=
  PatternTransport.scopeBack
    (SubexpMainPhysicalSystem.system_toPattern G hG hell hcap hD).symm e v

theorem scopeBack_val (e : Fin (SubexpLeafScopeOrder.rawScopes G hG hell).length)
    (v : {v // v ∈ (SubexpMainPhysicalSystem.system G hG hell hcap hD).scope e}) :
    (scopeBack G hG hell hcap hD e v).val = v.val :=
  PatternTransport.scopeBack_val
    (SubexpMainPhysicalSystem.system_toPattern G hG hell hcap hD).symm e v

theorem color : (SubexpMainPhysicalSystem.layout G hG hell hcap hD L).color = L.color :=
  PatternTransport.color (SubexpMainPhysicalSystem.system_toPattern G hG hell hcap hD).symm L

theorem row (e : Fin (SubexpLeafScopeOrder.rawScopes G hG hell).length)
    (v : {v // v ∈ (SubexpMainPhysicalSystem.system G hG hell hcap hD).scope e}) (w : Fin D) :
    (SubexpMainPhysicalSystem.layout G hG hell hcap hD L).row e v w =
      L.row e (scopeBack G hG hell hcap hD e v) w :=
  PatternTransport.row (SubexpMainPhysicalSystem.system_toPattern G hG hell hcap hD).symm L e v w

theorem row_at (e : Fin (SubexpLeafScopeOrder.rawScopes G hG hell).length)
    (v w : Fin D)
    (hv : v ∈ (Subexp.IncidencePlanSpec.pattern D (SubexpLeafScopeOrder.rawScopes G hG hell)).scope e)
    (hv' : v ∈ (SubexpMainPhysicalSystem.system G hG hell hcap hD).scope e) :
    (SubexpMainPhysicalSystem.layout G hG hell hcap hD L).row e ⟨v, hv'⟩ w =
      L.row e ⟨v, hv⟩ w :=
  PatternTransport.row_at (SubexpMainPhysicalSystem.system_toPattern G hG hell hcap hD).symm L e v w hv hv'

end SubexponentialSAT.SubexpMainPhysicalLayoutRows

end OAI.Algorithms
