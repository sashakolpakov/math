import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWideLoop

namespace OAI.Algorithms

/-! The reusable node workspace. Only physically populated permanent
masters may be occupied between visits. The active node and the returned
jet/shape occupy three additional ports while a visit is in progress. -/

namespace SubexponentialSAT.SubexpNodeWorkspace

abbrev Store := Fin 288 → List Bool

def MasterPort (i : Fin 288) : Prop :=
  i = 5 ∨ i = 10 ∨ i = 25 ∨ i = 91 ∨ i = 92 ∨ i = 109 ∨
    (119 ≤ i.val ∧ i.val < 138) ∨ 255 ≤ i.val

instance (i : Fin 288) : Decidable (MasterPort i) := by
  unfold MasterPort
  infer_instance

def initialStacks (masters : Store) : Store :=
  fun i => if MasterPort i then masters i else []

def Ready (masters current : Store) : Prop := current = initialStacks masters

def activeStacks (masters : Store) (node : List Bool) : Store :=
  Function.update (initialStacks masters) 78 node

def finalStacks (masters : Store) (jet shape : List Bool) : Store :=
  Function.update (Function.update (initialStacks masters) 102 jet) 104 shape

@[simp] theorem initial_empty (masters : Store) (i : Fin 288) (hi : ¬ MasterPort i) :
    initialStacks masters i = [] := by simp only [initialStacks, ite_eq_right hi]

@[simp] theorem initial_master (masters : Store) (i : Fin 288) (hi : MasterPort i) :
    initialStacks masters i = masters i := by simp only [initialStacks, ite_eq_left hi]

theorem ready_empty {masters current : Store} (h : Ready masters current)
    (i : Fin 288) (hi : ¬ MasterPort i) : current i = [] := by
  rw [h]
  exact initial_empty masters i hi

theorem ready_master {masters current : Store} (h : Ready masters current)
    (i : Fin 288) (hi : MasterPort i) : current i = masters i := by
  rw [h]
  exact initial_master masters i hi

theorem active_from_ready {masters current : Store} (node : List Bool)
    (h : Ready masters (Function.update current 78 [])) (hn : current 78 = node) :
    current = activeStacks masters node := by
  funext i
  by_cases hi : i = 78
  · subst i
    simpa [activeStacks] using hn
  · have he := congrFun h i
    simpa only [activeStacks, Function.update_of_ne hi] using he

theorem active_empty (masters : Store) (node : List Bool) (i : Fin 288)
    (hi : ¬ MasterPort i) (hn : i ≠ 78) : activeStacks masters node i = [] := by
  simp only [activeStacks, Function.update_of_ne hn, initial_empty masters i hi]

theorem active_master (masters : Store) (node : List Bool) (i : Fin 288)
    (hi : MasterPort i) : activeStacks masters node i = masters i := by
  have hn : i ≠ 78 := by
    intro he
    subst i
    exact (show ¬ MasterPort (78 : Fin 288) from by decide) hi
  simp only [activeStacks, Function.update_of_ne hn, initial_master masters i hi]

theorem final_ready (masters : Store) (jet shape : List Bool) :
    Ready masters (Function.update (Function.update (finalStacks masters jet shape) 102 []) 104 []) := by
  funext i
  by_cases h102 : i = 102
  · subst i
    simp [finalStacks, initialStacks, MasterPort, Fin.coe_ofNat_eq_mod]
  by_cases h104 : i = 104
  · subst i
    simp [finalStacks, initialStacks, MasterPort, Fin.coe_ofNat_eq_mod]
  · simp [finalStacks,h102,h104]

theorem protected_master (i : Fin 288) (hi : SubexpNodeWideLoop.ProtectedBank i) :
    MasterPort i := by
  rcases hi with hi | hi
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,hi.2⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))))

theorem final_protected (masters : Store) (node jet shape : List Bool)
    (i : Fin 288) (hi : SubexpNodeWideLoop.ProtectedBank i) :
    finalStacks masters jet shape i = activeStacks masters node i := by
  have hm := protected_master i hi
  have h102 : i ≠ 102 := by
    intro he; subst i
    exact (show ¬ MasterPort (102 : Fin 288) from by decide) hm
  have h104 : i ≠ 104 := by
    intro he; subst i
    exact (show ¬ MasterPort (104 : Fin 288) from by decide) hm
  rw [active_master masters node i hm]
  simp only [finalStacks, Function.update_of_ne h104, Function.update_of_ne h102,
    initial_master masters i hm]

end SubexponentialSAT.SubexpNodeWorkspace

end OAI.Algorithms
