import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNativeSemantics

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

/-- The actual accumulator at every callback may have different bytes. Only
its denotation participates in the ordered product identity. -/
theorem runRel_denote {n B d : ℕ} {R : Type*} [CommRing R]
    (u J : ℕ) (decode : Raw n B d → Jet (Fin n) R)
    (value : ℕ → Jet (Fin n) R) (step : Raw n B d → ℕ → Raw n B d → Prop)
    (hstep : ∀ a id b, step a id b → decode b=canonical u J (decode a*value id))
    {ids : List ℕ} {seed out : Raw n B d} (hr : RunRel step ids seed out)
    (start : Jet (Fin n) R) (hs : decode seed=canonical u J start) :
    decode out=canonical u J (start*(ids.map value).prod) := by
  induction hr generalizing start with
  | nil a => simpa using hs
  | @cons id ids a b c hab hbc ih =>
    have hb := hstep a id b hab
    rw [hs,Moments.canonical_mul_left] at hb
    simpa only [List.map_cons,List.prod_cons,mul_assoc] using ih (start*value id) hb

/-- Starting from a stored one yields the product of precisely the parsed IDs. -/
theorem runRel_product {n B d : ℕ} {R : Type*} [CommRing R]
    (u J : ℕ) (decode : Raw n B d → Jet (Fin n) R)
    (value : ℕ → Jet (Fin n) R) (step : Raw n B d → ℕ → Raw n B d → Prop)
    (hstep : ∀ a id b, step a id b → decode b=canonical u J (decode a*value id))
    {ids : List ℕ} {one out : Raw n B d} (hr : RunRel step ids one out)
    (hone : decode one=canonical u J 1) :
    decode out=canonical u J (ids.map value).prod := by
  simpa only [one_mul] using runRel_denote u J decode value step hstep hr 1 hone
end SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop

end OAI.Algorithms
