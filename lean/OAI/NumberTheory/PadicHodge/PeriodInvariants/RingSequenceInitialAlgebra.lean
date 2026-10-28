import OAI.NumberTheory.PadicHodge.PeriodInvariants.RingSequenceColimitElements
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Ring Sequence Initial Algebra -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.RingSequenceInitialAlgebra

noncomputable section

/-! # A ring sequence and its colimit carry their canonical initial-ring coefficients -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u
variable (F : ℕ ⥤ CommRingCat.{u}) [HasColimit F]

@[instance_reducible]
def stageAlgebra (n : ℕ) : Algebra (F.obj 0) (F.obj n) :=
  (F.map (homOfLE (Nat.zero_le n))).hom.toAlgebra

@[instance_reducible]
def limitAlgebra : Algebra (F.obj 0) ↑(colimit F) := (colimit.ι F 0).hom.toAlgebra

attribute [local instance] stageAlgebra limitAlgebra

def transition (i j : ℕ) (h : i ≤ j) : F.obj i →ₐ[F.obj 0] F.obj j where
  __ := (F.map (homOfLE h)).hom
  commutes' r :=
    (congrArg (fun q : F.obj 0 ⟶ F.obj j => q.hom r)
      (F.map_comp (homOfLE (Nat.zero_le i)) (homOfLE h))).symm

def inclusion (n : ℕ) : F.obj n →ₐ[F.obj 0] ↑(colimit F) where
  __ := (colimit.ι F n).hom
  commutes' r := congrArg (fun q : F.obj 0 ⟶ colimit F => q.hom r)
    (colimit.w F (homOfLE (Nat.zero_le n)))

theorem inclusion_transition (i j : ℕ) (h : i ≤ j) (a : F.obj i) :
    inclusion F j (transition F i j h a) = inclusion F i a :=
  RingSequenceColimitElements.transition F i j h a

theorem inclusion_injective
    (hf : ∀ i j (h : i ≤ j), Function.Injective (F.map (homOfLE h)).hom) (n : ℕ) :
    Function.Injective (inclusion F n) := RingSequenceColimitElements.inclusion_injective F hf n

theorem finite_representatives (s : Finset ↑(colimit F)) :
    ∃ i, ∃ y : s → F.obj i, ∀ j, inclusion F i (y j) = j.val :=
  RingSequenceColimitElements.exists_reps F (fun j : s => j.val)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.RingSequenceInitialAlgebra
