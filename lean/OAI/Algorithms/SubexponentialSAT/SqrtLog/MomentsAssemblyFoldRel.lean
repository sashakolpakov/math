import Mathlib.Data.List.Defs

/-! The execution-associated relational fold used by moment assembly. Keeping
this relation in its own module lets machine proofs depend on the relation
without importing the materializing moment-assembly programs. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssembly.Relational

inductive FoldRel {A W : Type*} (step : A → W → A → Prop) :
    List W → A → A → Prop
  | nil (a) : FoldRel step [] a a
  | cons {x xs a b c} : step a x b → FoldRel step xs b c → FoldRel step (x :: xs) a c

end OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssembly.Relational
