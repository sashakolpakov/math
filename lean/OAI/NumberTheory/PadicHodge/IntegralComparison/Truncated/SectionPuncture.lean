import OAI.NumberTheory.PadicHodge.IntegralComparison.SectionPuncturePullback
import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.WittFinite
import Mathlib.RingTheory.Artinian.Ring

/-! # Section Puncture -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SectionPuncture

noncomputable section

/-! Compatible original sections have the same puncture on the
special fiber of a truncated Witt model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (n : ℕ)

theorem reduction_surjective : Function.Surjective
    (Spec.map (CommRingCat.ofHom (Witt.reduction p k n))) := by
  let : Finite (Witt.Ring p k n) := WittFinite.finite p k n
  let : Nontrivial (Witt.Ring p k n) :=
    Function.Surjective.nontrivial (Witt.reduction_surjective p k n)
  let : IsLocalRing (Witt.Ring p k n) :=
    IsLocalRing.of_surjective' (Witt.quotient p k n) Ideal.Quotient.mk_surjective
  let : Subsingleton (Spec (CommRingCat.of (Witt.Ring p k n))) :=
    Ring.KrullDimLE.subsingleton_primeSpectrum (Witt.Ring p k n)
  intro t
  exact ⟨Classical.ofNonempty, Subsingleton.elim _ _⟩

variable
  (X : Over (Spec (CommRingCat.of (Witt.Ring p k n))))
  (Y : Over (Spec (CommRingCat.of k))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Witt.reduction p k n))))
  (s : Spec (CommRingCat.of (Witt.Ring p k n)) ⟶ X.left)
  (s₀ : Spec (CommRingCat.of k) ⟶ Y.left)
  [IsClosedImmersion s] [IsClosedImmersion s₀]
  (hred : s₀ ≫ f = Spec.map (CommRingCat.ofHom (Witt.reduction p k n)) ≫ s)

include hp hred in
theorem outside : f ⁻¹ᵁ SectionIdealPuncturedCover.outside s.ker =
    SectionIdealPuncturedCover.outside s₀.ker := by
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Witt.reduction p k n))) :=
    IsClosedImmersion.spec_of_surjective _ (Witt.reduction_surjective p k n)
  let : IsClosedImmersion f := MorphismProperty.of_isPullback hp.flip inferInstance
  exact SectionPuncturePullback.outside f _ s s₀ hred
    f.isClosedEmbedding.injective (reduction_surjective p k n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SectionPuncture
