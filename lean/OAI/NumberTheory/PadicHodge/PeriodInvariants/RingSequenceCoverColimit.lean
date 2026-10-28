import OAI.NumberTheory.PadicHodge.PeriodInvariants.RingSequenceInitialAlgebra
import OAI.NumberTheory.PadicHodge.PeriodInvariants.FaithfullyFlatRingUnion
import OAI.NumberTheory.PadicHodge.PeriodInvariants.WeaklyEtaleUnion
import OAI.NumberTheory.PadicHodge.PeriodInvariants.WeaklyEtaleRingHom
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-! # Ring Sequence Cover Colimit -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.RingSequenceCoverColimit

noncomputable section

/-! # Sequential colimits of faithfully flat weakly etale ring maps are covering maps -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits OAI.NumberTheory.PadicHodge.PeriodInvariants.RingSequenceInitialAlgebra

attribute [local instance] RingSequenceInitialAlgebra.stageAlgebra
  RingSequenceInitialAlgebra.limitAlgebra

universe u
variable (F : ℕ ⥤ CommRingCat.{u}) [HasColimit F]
  (hf : ∀ i j (h : i ≤ j), (F.map (homOfLE h)).hom.FaithfullyFlat)

include hf

theorem faithfullyFlat : (colimit.ι F 0).hom.FaithfullyFlat := by
  have (n : ℕ) : Module.FaithfullyFlat (F.obj 0) (F.obj n) := hf 0 n (Nat.zero_le n)
  change Module.FaithfullyFlat (F.obj 0) ↑(colimit F)
  exact FaithfullyFlatRingUnion.faithfullyFlat (fun n => ↑(F.obj n)) (RingSequenceInitialAlgebra.inclusion F)
    (RingSequenceInitialAlgebra.inclusion_injective F (fun i j h => (hf i j h).injective)) (RingSequenceInitialAlgebra.finite_representatives F)

theorem weaklyEtale
    (hw : ∀ n, WeaklyEtaleRingHom.Property (F.map (homOfLE (Nat.zero_le n))).hom) :
    WeaklyEtaleRingHom.Property (colimit.ι F 0).hom := by
  have : Module.FaithfullyFlat (F.obj 0) ↑(colimit F) := faithfullyFlat F hf
  have (n : ℕ) : Algebra.WeaklyEtale (F.obj 0) (F.obj n) := hw n
  change Algebra.WeaklyEtale (F.obj 0) ↑(colimit F)
  exact WeaklyEtaleUnion.weaklyEtale (fun n => ↑(F.obj n)) (RingSequenceInitialAlgebra.inclusion F) (RingSequenceInitialAlgebra.transition F)
    (RingSequenceInitialAlgebra.inclusion_transition F) (RingSequenceColimitElements.exists_rep F)
    (RingSequenceInitialAlgebra.inclusion_injective F (fun i j h => (hf i j h).injective))

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.RingSequenceCoverColimit
