import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteMoments
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramConcreteMerge
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgramModel

namespace OAI.Algorithms

/-! The native mask predicate is exactly the free-head Boolean moment weight,
including ambient supports that are stored using original variable IDs. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open MomentsAssembly BucketTupleProgram.Concrete

variable {n r : ℕ} {R : Type*} [CommRing R]

def extendedHead (H : Finset (Fin n)) (head : ResidualEmbedding.Free H → Fin r)
    (v : Fin n) : Option (Fin r) :=
  if hv : v∉H then some (head ⟨v,hv⟩) else none

theorem headMask_extended (H : Finset (Fin n)) (head : ResidualEmbedding.Free H → Fin r)
    (g : Fin r) : List.ofFn (headMask H head g)=LeafWeightProgram.headBits (extendedHead H head) (some g) := by
  unfold LeafWeightProgram.headBits
  congr 1
  funext v
  by_cases hv : v∉H <;> simp [headMask,extendedHead,hv]

def nativeWeight (H : Finset (Fin n)) (head : ResidualEmbedding.Free H → Fin r)
    (s : Finset (Fin n)) (g : Fin r) (a : Moments.Head head g → Bool) : R :=
  if LeafWeightProgram.good (ambientEncode H head g a) (Squarefree.encodeMask s)
    (List.ofFn (headMask H head g)) then 1 else 0

theorem nativeWeight_map (H : Finset (Fin n)) (head : ResidualEmbedding.Free H → Fin r)
    (s : Finset (ResidualEmbedding.Free H)) (g : Fin r) (a : Moments.Head head g → Bool) :
    nativeWeight H head (s.map (ResidualEmbedding.inclusion H)) g a =
      Moments.localBoolWeight (R:=R) head ⟨s⟩ g a := by
  unfold nativeWeight
  rw [headMask_extended]
  change (if LeafWeightProgram.good (List.ofFn _) (LeafWeightProgram.supportBits ⟨_⟩)
    (LeafWeightProgram.headBits (extendedHead H head) (some g)) then (1:R) else 0)=_
  rw [LeafWeightProgram.localBoolWeight_eq]
  unfold Moments.localBoolWeight
  erw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro v hv
  have hext : extendedHead H head (ResidualEmbedding.inclusion H v) = some (head v) := by
    change (if hv : v.val ∉ H then some (head ⟨v.val, hv⟩) else none) = some (head v)
    rw [dite_eq_left v.property]
  by_cases hg : head v=g
  · have heq : extendedHead H head (ResidualEmbedding.inclusion H v) = some g :=
      hext.trans (congrArg some hg)
    rw [dite_eq_left heq, dite_eq_left hg]
    have hvalue :
        (if hv : (ResidualEmbedding.inclusion H v) ∉ H then
            if hhead : head ⟨ResidualEmbedding.inclusion H v, hv⟩ = g then
              a ⟨⟨ResidualEmbedding.inclusion H v, hv⟩, hhead⟩
            else false
          else false) = a ⟨v, hg⟩ := by
      change (if hv : v.val ∉ H then
          if hhead : head ⟨v.val, hv⟩ = g then a ⟨⟨v.val, hv⟩, hhead⟩
          else false else false) = a ⟨v, hg⟩
      rw [dite_eq_left v.property, dite_eq_left hg]
    exact congrArg (fun b : Bool => if b then (1 : R) else 0) hvalue
  · have hneq : ¬ extendedHead H head (ResidualEmbedding.inclusion H v) = some g := by
      intro h
      exact hg (Option.some.inj (hext.symm.trans h))
    rw [dite_eq_right hneq, dite_eq_right hg]

theorem nativeWeight_partition (H : Finset (Fin n)) (head : ResidualEmbedding.Free H → Fin r)
    (s : Finset (ResidualEmbedding.Free H)) (a : ∀ g,Moments.Head head g → Bool) :
    Moments.jetConstant (Squarefree.weight (Squarefree.boolValue (R:=R) (Moments.assemble head a)) s) =
      ∏ g,Moments.jetConstant (nativeWeight H head (s.map (ResidualEmbedding.inclusion H)) g (a g)) := by
  simp_rw [nativeWeight_map]
  rw [Moments.boolWeight_partition head ⟨s⟩ a]
  simp only [Moments.jetConstant,map_prod]

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
