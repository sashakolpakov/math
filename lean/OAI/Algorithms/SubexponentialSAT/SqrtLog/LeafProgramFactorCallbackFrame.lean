import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorRecord

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls

theorem hash_updates (s : Fin 768 → List Bool) (payload value : List Bool)
    (h154 : s 154=[]) (h64 : s 64=[]) (h67 : s 67=[]) (h68 : s 68=[]) (h62 : s 62=[]) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update s 154 payload) 154 []) 64 []) 67 []) 68 []) 62 []) 151 value =
      Function.update s 151 value := by
  funext i
  by_cases h : i=151
  · subst i; simp
  by_cases h' : i=62
  · subst i; simp [h62]
  by_cases h'' : i=68
  · subst i; simp [h68]
  by_cases h''' : i=67
  · subst i; simp [h67]
  by_cases h4 : i=64
  · subst i; simp [h64]
  by_cases h5 : i=154
  · subst i; simp [h154]
  simp [h,h',h'',h''',h4,h5]

theorem marked_updates (s : Fin 768 → List Bool) (payload value : List Bool)
    (h154 : s 154=[]) (h63 : s 63=[]) (h67 : s 67=[]) (h62 : s 62=[]) :
    Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update s 154 payload) 154 []) 63 []) 67 []) 62 []) 151 value =
      Function.update s 151 value := by
  funext i
  by_cases h : i=151
  · subst i; simp
  by_cases h' : i=62
  · subst i; simp [h62]
  by_cases h'' : i=67
  · subst i; simp [h67]
  by_cases h''' : i=63
  · subst i; simp [h63]
  by_cases h4 : i=154
  · subst i; simp [h154]
  simp [h,h',h'',h''',h4]

theorem callback_updates (s : Fin 768 → List Bool) (value : List Bool) :
    Function.update (Function.update s 151 value) 149 [] =
      Function.update (Function.update s 149 []) 151 value := by
  funext i
  by_cases h : i=149
  · subst i; simp
  by_cases h' : i=151
  · subst i; simp
  simp [h,h']

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
