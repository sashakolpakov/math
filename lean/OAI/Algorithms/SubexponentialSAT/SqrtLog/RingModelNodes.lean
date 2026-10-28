import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel
import OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation

namespace OAI.Algorithms

/-! Explicit radix-indexed nodes for the supplied-polynomial ring model. -/

noncomputable section
namespace SubexponentialSAT.SqrtLog.RingModel.Data

variable {d : ℕ} (a : RingModel.Data d) (t Q : ℕ)

/-- Index a residue by its base-three coefficient digits. -/
def fieldIndex : a.E ≃ Fin (3 ^ d) :=
  a.fieldCoordinates.toEquiv.trans
    ((Equiv.piCongrRight fun _ : Fin d => (ZMod.finEquiv 3).symm.toEquiv).trans
      finFunctionFinEquiv)

@[simp] theorem fieldIndex_zero : a.fieldIndex 0 = 0 := by
  apply Fin.ext
  simp [fieldIndex ]

/-- Node i is the residue whose coefficient word has radix index i+1. -/
def residueNode (hQ : Q < 3 ^ d) (i : Fin Q) : a.E :=
  a.fieldIndex.symm ⟨i.val + 1, by omega⟩

theorem residueNode_ne_zero (hQ : Q < 3 ^ d) (i : Fin Q) :
    a.residueNode Q hQ i ≠ 0 := by
  intro he
  have hh := congrArg a.fieldIndex he
  simp only [residueNode, Equiv.apply_symm_apply, fieldIndex_zero] at hh
  have hv := congrArg Fin.val hh
  simp only [Fin.val_zero] at hv
  omega

theorem residueNode_injective (hQ : Q < 3 ^ d) :
    Function.Injective (a.residueNode Q hQ) := by
  intro i j hij
  have hh := congrArg a.fieldIndex hij
  simp only [residueNode, Equiv.apply_symm_apply] at hh
  have hv : i.val + 1 = j.val + 1 := congrArg (fun z : Fin (3 ^ d) => z.val) hh
  apply Fin.ext
  omega

def node (ht : 0 < t) (hQ : Q < 3 ^ d) (i : Fin Q) : a.O t :=
  a.sectionValue t ht (a.residueNode Q hQ i)

@[simp] theorem rho_node (ht : 0 < t) (hQ : Q < 3 ^ d) (i : Fin Q) :
    a.rho t ht (a.node t Q ht hQ i) = a.residueNode Q hQ i := a.rho_sectionValue t ht _

def inverseValue (ht : 0 < t) (x : a.O t) : a.O t :=
  NilpotentDefect.residueInverse (a.rho t ht) (a.sectionValue t ht) t x

theorem mul_inverseValue (ht : 0 < t) (x : a.O t) (hx : a.rho t ht x ≠ 0) :
    x * a.inverseValue t ht x = 1 :=
  NilpotentDefect.mul_residueInverse (a.rho t ht) (a.sectionValue t ht)
    (a.rho_sectionValue t ht) (3 : a.O t) t (a.prime_power_zero t)
    (fun z hz => (a.rho_eq_zero_iff t ht z).mp hz) x hx

def unitOfResidue (ht : 0 < t) (x : a.O t) (hx : a.rho t ht x ≠ 0) : (a.O t)ˣ where
  val := x
  inv := a.inverseValue t ht x
  val_inv := a.mul_inverseValue t ht x hx
  inv_val := by rw [mul_comm]; exact a.mul_inverseValue t ht x hx

@[simp] theorem unitOfResidue_val (ht : 0 < t) (x : a.O t) (hx : a.rho t ht x ≠ 0) :
    (a.unitOfResidue t ht x hx : a.O t) = x := rfl

theorem node_isUnit (ht : 0 < t) (hQ : Q < 3 ^ d) (i : Fin Q) :
    IsUnit (a.node t Q ht hQ i) := by
  apply a.isUnit_of_rho_ne_zero t ht
  rw [rho_node]
  exact a.residueNode_ne_zero Q hQ i

theorem difference_isUnit (ht : 0 < t) (hQ : Q < 3 ^ d) (i j : Fin Q) (hij : i ≠ j) :
    IsUnit (a.node t Q ht hQ i - a.node t Q ht hQ j) := by
  apply a.isUnit_of_rho_ne_zero t ht
  rw [map_sub, rho_node, rho_node]
  exact sub_ne_zero.mpr (fun he => hij (a.residueNode_injective Q hQ he))

def nodeUnits (ht : 0 < t) (hQ : Q < 3 ^ d) :
    SubexpRowInterpolation.NodeUnits (a.node t Q ht hQ) where
  nodeUnit i := a.unitOfResidue t ht (a.node t Q ht hQ i) (by
    rw [rho_node]; exact a.residueNode_ne_zero Q hQ i)
  nodeUnit_val _ := rfl
  differenceUnit i j hij := a.unitOfResidue t ht (a.node t Q ht hQ i - a.node t Q ht hQ j) (by
    rw [map_sub, rho_node, rho_node]
    exact sub_ne_zero.mpr (fun he => hij (a.residueNode_injective Q hQ he)))
  differenceUnit_val _ _ _ := rfl

end SubexponentialSAT.SqrtLog.RingModel.Data

end
end OAI.Algorithms
