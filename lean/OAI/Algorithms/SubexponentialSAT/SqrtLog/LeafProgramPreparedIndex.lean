import OAI.Algorithms.SubexponentialSAT.LeanCompat

import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

universe u v w

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

def transportFamily {I : Sort u} (F : I → Sort v) {i j : I} (h : i=j) (x : F i) : F j := h ▸ x

theorem observe_transport {I : Sort u} (F : I → Sort v) {A : Sort w}
    (observe : ∀i,F i → A) {i j : I} (h : i=j) (x : F i) :
    observe j (transportFamily F h x)=observe i x := by
  cases h
  rfl

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
