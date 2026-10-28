import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedNodePostModel

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodePost
open SubexponentialSAT MomentsAssembly MomentsAssembly.Relational NodeNative

theorem reachable_parameters {n B B' d u u' J J' : ℕ}
    (vars : Finset (Fin n)) (P : (Fin 768 → List Bool) → Prop)
    (high : Fin 768 → List Bool) (ss : List (Finset (Fin n))) (bs : List BucketInput)
    (hB : B=B') (hu : u=u') (hJ : J=J')
    (h : Reachable.BucketFrames B d vars u J P high ss bs) :
    Reachable.BucketFrames B' d vars u' J' P high ss bs := by
  subst B'; subst u'; subst J'; exact h

theorem budget_parameters {s : HeadInputs} {a b : NodeNative.Data}
    (pr : Preparation s a b) {B B' d u u' J J' H X Y A W K : ℕ}
    (hB : B=B') (hu : u=u') (hJ : J=J')
    (h : fullBudget pr B d u J H X Y A W ≤ K) :
    fullBudget pr B' d u' J' H X Y A W ≤ K := by
  subst B'; subst u'; subst J'; exact h

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodePost

end OAI.Algorithms
