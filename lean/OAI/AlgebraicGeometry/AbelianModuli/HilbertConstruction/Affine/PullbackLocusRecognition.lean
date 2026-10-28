import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.MonoRecognition
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SubfunctorRepresentations
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-! # Pullback Locus Recognition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PullbackLocusRecognition

noncomputable section

/-! A represented affine lifting condition identifies the actual pullback of a monomorphism as a quasi-compact locally closed immersion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry OAI.AlgebraicGeometry.HilbertScheme.Presentations.SubfunctorRepresentations

universe u

variable {S : Scheme.{u}} {G Z M : Over S}
variable (p : Z ⟶ G) [Mono p] (g : M ⟶ G)

theorem pullback_snd_lift_iff {T : Over S} (x : T ⟶ M) :
    (∃ a : T ⟶ pullback p g, a ≫ pullback.snd p g = x) ↔
      ∃! y : T ⟶ Z, y ≫ p = x ≫ g := by
  constructor
  · rintro ⟨a, ha⟩
    have hy : (a ≫ pullback.fst p g) ≫ p = x ≫ g := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, ha]
    exact ⟨a ≫ pullback.fst p g, hy, fun y hy' => (cancel_mono p).mp (hy'.trans hy.symm)⟩
  · rintro ⟨y, hy, _⟩
    exact ⟨pullback.lift y x hy, pullback.lift_snd y x hy⟩

theorem pullback_locus_of_affine_lifts (F : Subfunctor (yoneda.obj M)) (hF : HilbertScheme.Presentations.SubfunctorRepresentations.ImmersionRepresentable F)
    (h : ∀ (R : CommRingCat.{u}) (f : Spec R ⟶ S) (x : Over.mk f ⟶ M),
      x ∈ F.obj (.op (Over.mk f)) ↔ ∃! y : Over.mk f ⟶ Z, y ≫ p = x ≫ g) :
    IsImmersion (pullback.snd p g).left ∧ QuasiCompact (pullback.snd p g).left := by
  obtain ⟨W, j, hj, hqc, e, he⟩ := hF
  let := hj
  let := hqc
  have : Mono j := Over.mono_of_mono_left j
  obtain ⟨i, hi⟩ := MonoRecognition.overMono_iso_of_affine_lifts (pullback.snd p g) j (fun R f x =>
    (pullback_snd_lift_iff p g x).trans ((h R f x).symm.trans
      (HilbertScheme.Presentations.SubfunctorRepresentations.represented_subfunctor_mem F j e he (Over.mk f) x)))
  have hleft : i.hom.left ≫ j.left = (pullback.snd p g).left := congrArg Over.Hom.left hi
  have : IsIso i.hom.left := inferInstanceAs (IsIso ((Over.forget S).map i.hom))
  rw [← hleft]
  exact ⟨inferInstance, inferInstance⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PullbackLocusRecognition
