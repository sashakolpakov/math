import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticMachine
import OAI.Algorithms.SubexponentialSAT.FourWordPrograms

namespace OAI.Algorithms

/-! Data layout for the fixed flat-record quartic multiplication program. -/

namespace SubexponentialSAT.SubexpQuarticFlatMul

open BitProgram StackRoutines StructuredCalls
open SubexpQuarticRing SubexpQuarticMachine

attribute [local simp] Fin.coe_ofNat_eq_mod Fin.ext_iff

def wordLists {B : ℕ} (q : Quad (Word B)) : FourWordPrograms.Words :=
  fun i => (q.toFn i).val

def flat {B : ℕ} (q : Quad (Word B)) : List Bool :=
  FourWordPrograms.flatWords (wordLists q)

@[simp] theorem wordLists_length {B : ℕ} (q : Quad (Word B)) (i : Fin 4) :
    (wordLists q i).length = B := (q.toFn i).property

@[simp] theorem flat_length {B : ℕ} (q : Quad (Word B)) : (flat q).length = 4 * B := by
  simp [flat, FourWordPrograms.flatWords]
  omega

def firstBank {B : ℕ} (t a b : Quad (Word B)) : Fin 12 → Word B :=
  fun i => Fin.addCases (m := 4) (n := 8) t.toFn
    (fun j => Fin.addCases (m := 4) (n := 4) a.toFn b.toFn j) i

def initialBank {B : ℕ} (t a b : Quad (Word B)) : Fin 61 → Word B :=
  fun i => Fin.addCases (m := 12) (n := 49) (firstBank t a b) (fun _ => a.c0) i

def partialBank {B : ℕ} (t a b : Quad (Word B)) : Fin 61 → List Bool :=
  fun i => Fin.addCases (m := 12) (n := 49) (fun j => (firstBank t a b j).val)
    (fun _ => []) i

@[simp] theorem initialBank_reduction {B : ℕ} (t a b : Quad (Word B)) :
    mulReduction (initialBank t a b) = t := by cases t; rfl

@[simp] theorem initialBank_left {B : ℕ} (t a b : Quad (Word B)) :
    mulLeft (initialBank t a b) = a := by cases a; rfl

@[simp] theorem initialBank_right {B : ℕ} (t a b : Quad (Word B)) :
    mulRight (initialBank t a b) = b := by cases b; rfl

/-- Bank 0–60, modulus 66, output 72, reduction cache 73, unary width 74.
All remaining local stacks are empty at routine boundaries. -/
def bankStore (bank : Fin 61 → List Bool) (modulus reduction width output : List Bool)
    (j : Fin 77) : List Bool :=
  if h : j.val < 61 then bank ⟨j.val, h⟩
  else if j = 66 then modulus
  else if j = 72 then output
  else if j = 73 then reduction
  else if j = 74 then width
  else []

def initialStore {B : ℕ} (modulus width : List Bool) (t a b : Quad (Word B)) :
    Stacks (Fin 77) :=
  Function.update (Function.update (bankStore (fun _ => []) modulus (flat t) width [])
    70 (flat a)) 71 (flat b)

def finalStore {B : ℕ} (modulus width : List Bool) (t result : Quad (Word B)) :
    Stacks (Fin 77) :=
  bankStore (fun _ => []) modulus (flat t) width (flat result)

@[simp] theorem bankStore_bank (bank : Fin 61 → List Bool)
    (modulus reduction width output : List Bool) (i : Fin 61) :
    bankStore bank modulus reduction width output (Fin.castAdd 16 i) = bank i := by
  simp [bankStore]

@[simp] theorem bankStore_modulus (bank : Fin 61 → List Bool)
    (modulus reduction width output : List Bool) :
    bankStore bank modulus reduction width output 66 = modulus := by norm_num [bankStore]

@[simp] theorem bankStore_output (bank : Fin 61 → List Bool)
    (modulus reduction width output : List Bool) :
    bankStore bank modulus reduction width output 72 = output := by norm_num [bankStore]

@[simp] theorem bankStore_reduction (bank : Fin 61 → List Bool)
    (modulus reduction width output : List Bool) :
    bankStore bank modulus reduction width output 73 = reduction := by norm_num [bankStore]

@[simp] theorem bankStore_width (bank : Fin 61 → List Bool)
    (modulus reduction width output : List Bool) :
    bankStore bank modulus reduction width output 74 = width := by norm_num [bankStore]

def splitReductionPorts : Fin 8 ↪ Fin 77 :=
  ⟨![75,74,76,69,0,1,2,3], by decide⟩

def splitLeftPorts : Fin 8 ↪ Fin 77 :=
  ⟨![70,74,76,69,4,5,6,7], by decide⟩

def splitRightPorts : Fin 8 ↪ Fin 77 :=
  ⟨![71,74,76,69,8,9,10,11], by decide⟩

def packPorts : Fin 8 ↪ Fin 77 :=
  ⟨![72,74,76,69,57,58,59,60], by decide⟩

def tempSlots : List (Fin 77) :=
  List.ofFn (fun i : Fin 49 => Fin.castAdd 16 (Fin.natAdd 12 i))

def bankSlots : List (Fin 77) :=
  List.ofFn (fun i : Fin 61 => Fin.castAdd 16 i)

@[simp] theorem tempSlots_length : tempSlots.length = 49 := by simp [tempSlots]
@[simp] theorem bankSlots_length : bankSlots.length = 61 := by simp [bankSlots]

theorem tempSlots_nodup : tempSlots.Nodup := by
  apply List.nodup_ofFn_ofInjective
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

theorem bankSlots_nodup : bankSlots.Nodup :=
  List.nodup_ofFn_ofInjective (Fin.castAdd_injective 61 16)

@[simp] theorem mem_tempSlots (j : Fin 77) :
    j ∈ tempSlots ↔ 12 ≤ j.val ∧ j.val < 61 := by
  simp only [tempSlots, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    simp only [Fin.val_castAdd, Fin.val_natAdd]
    omega
  · rintro ⟨hlo, hhi⟩
    refine ⟨⟨j.val - 12, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [Fin.val_castAdd, Fin.val_natAdd]
    omega

@[simp] theorem mem_bankSlots (j : Fin 77) : j ∈ bankSlots ↔ j.val < 61 := by
  simp only [bankSlots, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    exact i.isLt
  · intro hj
    exact ⟨⟨j.val, hj⟩, rfl⟩

def bankPorts : Fin 70 ↪ Fin 77 := ⟨Fin.castAdd 7, Fin.castAdd_injective 70 7⟩

end SubexponentialSAT.SubexpQuarticFlatMul

end OAI.Algorithms
