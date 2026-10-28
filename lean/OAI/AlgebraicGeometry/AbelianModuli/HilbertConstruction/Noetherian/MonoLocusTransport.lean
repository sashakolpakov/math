import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.AffineCoverLifts
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Mono Locus Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.MonoLocusTransport

noncomputable section

/-! Equivalent lifting conditions on locally Noetherian tests
identify actual monomorphic parameter loci, provided the loci and
the ambient pullback are locally Noetherian. The resulting square
is Cartesian on all tests. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {M N X Y : Over S}
variable (i : X ⟶ M) (j : Y ⟶ N) (a : N ⟶ M) [Mono i] [Mono j]
variable [IsLocallyNoetherian Y.left]
variable (H : ∀ (T : Over S), IsLocallyNoetherian T.left → ∀ x : T ⟶ N,
  (∃! u : T ⟶ X, u ≫ i = x ≫ a) ↔ (∃! v : T ⟶ Y, v ≫ j = x))

include H

omit [Mono i] in
theorem noetherianMonoLocusTransport_existsUnique :
    ∃! f : Y ⟶ X, f ≫ i = j ≫ a := by
  apply (H Y inferInstance j).mpr
  refine ⟨𝟙 Y, Category.id_comp j, fun v hv => ?_⟩
  exact (cancel_mono j).mp (hv.trans (Category.id_comp j).symm)

def noetherianMonoLocusTransport : Y ⟶ X :=
  (noetherianMonoLocusTransport_existsUnique i j a H).choose

omit [Mono i] in
theorem noetherianMonoLocusTransport_factor :
    noetherianMonoLocusTransport i j a H ≫ i = j ≫ a :=
  (noetherianMonoLocusTransport_existsUnique i j a H).choose_spec.1

theorem noetherianMonoLocusTransport_isPullback
    [IsLocallyNoetherian (pullback i a).left] :
    IsPullback (noetherianMonoLocusTransport i j a H) j i a := by
  obtain ⟨v, hv, _⟩ := (H (pullback i a) inferInstance (pullback.snd i a)).mp
    ⟨pullback.fst i a, pullback.condition,
      fun w hw => (cancel_mono i).mp (hw.trans pullback.condition.symm)⟩
  refine { w := noetherianMonoLocusTransport_factor i j a H, isLimit' := ⟨?_⟩ }
  apply PullbackCone.isLimitAux'
  intro s
  let t := pullback.lift s.fst s.snd s.condition
  have ht : (t ≫ v) ≫ j = s.snd := by
    rw [Category.assoc, hv]
    exact pullback.lift_snd _ _ _
  refine ⟨t ≫ v, ?_, ht, ?_⟩
  · apply (cancel_mono i).mp
    change ((t ≫ v) ≫ noetherianMonoLocusTransport i j a H) ≫ i = s.fst ≫ i
    rw [Category.assoc, noetherianMonoLocusTransport_factor, ← Category.assoc, ht]
    exact s.condition.symm
  · intro w _ hw
    exact (cancel_mono j).mp (hw.trans ht.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.MonoLocusTransport
