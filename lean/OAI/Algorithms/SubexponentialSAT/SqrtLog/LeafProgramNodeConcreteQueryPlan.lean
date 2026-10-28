import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcretePlan
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputAddressedProvenance

namespace OAI.Algorithms

/-! Head coherence, low-owner support, and factor colors for the exact
addressed query plan stream. No semantic plan relation is supplied. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open PackingCallerProgram PackingIncidenceInput

variable (p : Problem)

def planHigh : Finset (Fin p.n) :=
  Finset.univ.filter (fun v=>p.mask.getD v.val false=true)

def addressedOwner (i : Fin (addressedEntries p.scopes p.n p.mask).length) : Fin p.n :=
  ProducedQueryRank.owner p (addressedIndex p.scopes p.n p.mask i)

def planHead (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) (t : Fin p.Q) (v : Fin p.n) : Fin p.r :=
  ProducedQueryRank.words p a tail (.inl v) t

def planColor (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) (t : Fin p.Q) (f : ℕ) : Fin p.r :=
  if hf:f < p.factors then ProducedQueryRank.words p a tail (.inr ⟨f,hf⟩) t else ⟨0,p.hr⟩

theorem planHigh_mask (v : Fin p.n) :
    p.mask.getD v.val false=decide (v∈planHigh p) := by
  simp only [planHigh,Finset.mem_filter,Finset.mem_univ,true_and]
  cases h:p.mask.getD v.val false <;> simp

theorem addressedOwner_get (i : Fin (addressedEntries p.scopes p.n p.mask).length) :
    ((addressedEntries p.scopes p.n p.mask).get i).1=(addressedOwner p i).val := by
  rw [addressedEntries_get]
  rfl

theorem addressedOwner_low (i : Fin (addressedEntries p.scopes p.n p.mask).length) :
    addressedOwner p i∉planHigh p := by
  have h := (addressed_owner_low p.scopes p.n p.mask i).2
  rw [addressedOwner_get p i] at h
  simp only [planHigh,Finset.mem_filter,Finset.mem_univ,true_and,h,Bool.false_eq_true,not_false_eq_true]

theorem addressedPlan_head (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (i : Fin (addressedEntries p.scopes p.n p.mask).length) (t : Fin p.Q) :
    ((addressedPacking p.scopes p.n p.mask (ProducedQueryRank.packing p a tail)).label i).head t =
      planHead p a tail t (addressedOwner p i) := by
  rw [addressedPacking_head]
  rfl

theorem addressedPlan_slot (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (t : Fin p.Q) (f j : ℕ) (hp : (j,p.n+f)∈addressedEntries p.scopes p.n p.mask) :
    ((addressedPacking p.scopes p.n p.mask (ProducedQueryRank.packing p a tail)).label
      (planIndex (addressedEntries p.scopes p.n p.mask) p.n f j hp)).slot 0 t=planColor p a tail t f := by
  let i := planIndex (addressedEntries p.scopes p.n p.mask) p.n f j hp
  have he := planIndex_get (addressedEntries p.scopes p.n p.mask) p.n f j hp
  have hf' := addressed_factor_of_get p.scopes p.n p.mask p.mask_le i j f he
  have hf : f < p.factors := by
    rw [←hf']
    exact (ProducedQueryRank.factor p (addressedIndex p.scopes p.n p.mask i)).isLt
  have hs := addressedPacking_slot_of_get p a tail i j ⟨f,hf⟩ he
  simp only [planColor,dite_eq_left hf]
  exact congrArg (fun w=>w t) hs

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
