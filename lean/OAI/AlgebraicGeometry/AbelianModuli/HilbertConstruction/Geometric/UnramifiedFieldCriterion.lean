import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedFlatDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeUnramifiedFieldCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FieldExtensionReflection
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Unramified Field Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.UnramifiedFieldCriterion

noncomputable section

/-! Locally finite-type morphisms are formally unramified if all algebraically closed field-valued base changes are formally unramified. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem formallyUnramified_of_geometricFieldPullbacks {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ Y),
      FormallyUnramified (pullback.snd f b)) : FormallyUnramified f := by
  apply SchemeUnramifiedFieldCriterion.formallyUnramified_of_fieldPullbacks f
  intro K _ b
  let φ : CommRingCat.of K ⟶ CommRingCat.of (AlgebraicClosure K) :=
    CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))
  have hflat : Flat (Spec.map φ) := Flat.SpecMap_iff.mpr
    (RingHom.flat_algebraMap_iff.mpr (inferInstanceAs (Module.Flat K (AlgebraicClosure K))))
  have hsurj : Surjective (Spec.map φ) := Smooth.FieldExtensionReflection.fieldSpecMap_surjective φ
  have hqc : QuasiCompact (Spec.map φ) := inferInstance
  have hgeom : FormallyUnramified (pullback.snd f (Spec.map φ ≫ b)) :=
    h (AlgebraicClosure K) (Spec.map φ ≫ b)
  have hiter : FormallyUnramified (pullback.snd (pullback.snd f b) (Spec.map φ)) :=
    UnramifiedPullbackRefinements.unramified_iterated_pullback f b (Spec.map φ)
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @FormallyUnramified) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (IsPullback.of_hasPullback (pullback.snd f b) (Spec.map φ)).flip
    ⟨⟨hsurj, hflat⟩, hqc⟩ hiter

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.UnramifiedFieldCriterion
