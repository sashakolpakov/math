import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PreparedNodeReadyBase
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryInput

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodeReady
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

private theorem cleanupPorts_321 : (321 : Fin 768) ∉ Node.cleanupPorts := by
  intro h
  have hh := (Node.mem_cleanup _).mp h
  norm_num at hh

private theorem cleanupPorts_705 : (705 : Fin 768) ∉ Node.cleanupPorts := by
  intro h
  have hh := (Node.mem_cleanup _).mp h
  norm_num at hh

private theorem cleanupPorts_706 : (706 : Fin 768) ∉ Node.cleanupPorts := by
  intro h
  have hh := (Node.mem_cleanup _).mp h
  norm_num at hh

theorem cleanup_unprotected (i : Fin 768) (hi : i∈Node.cleanupPorts) : ¬Query.Protected i := by
  have h := (Node.mem_cleanup i).mp hi
  simp only [Query.Protected,Fin.ext_iff,Fin.coe_ofNat_eq_mod]
  norm_num
  omega

theorem cleanWork_blank (a : Query.Data) (h : Query.CleanWork a) : NodeNative.Blank a := by
  intro i hi hn
  apply h i (cleanup_unprotected i hi)
  intro he
  subst i
  exact cleanupPorts_321 hi

theorem marked_blank (a : Query.Data) (h : NodeNative.Blank a) :
    NodeNative.Blank (Query.markedInput a) := by
  intro i hi hn
  by_cases ht : i=699
  · subst i; exact Query.markedInput_temporary a
  have h705 : i≠705 := by intro he; subst i; exact cleanupPorts_705 hi
  have h706 : i≠706 := by intro he; subst i; exact cleanupPorts_706 hi
  exact (Query.markedInput_frame a i ht h705 h706).trans (h i hi hn)

theorem unmarked_blank (a : Query.Data) (h : NodeNative.Blank a) :
    NodeNative.Blank (Query.unmarkedInput a) := by
  intro i hi hn
  have h705 : i≠705 := by intro he; subst i; exact cleanupPorts_705 hi
  have h706 : i≠706 := by intro he; subst i; exact cleanupPorts_706 hi
  exact (Query.unmarkedInput_frame a i h705 h706).trans (h i hi hn)

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodeReady

end OAI.Algorithms
