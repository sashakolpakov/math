import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Extension -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.Extension

/-! Every extension of fields is an affine faithfully flat cover, and its scheme pullback functor detects morphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {k K : Type u} [Field k] [Field K] (s : Spec (.of K) ⟶ Spec (.of k))

/-- Flatness follows from vector-space flatness, for an arbitrary actual field-spectrum map. -/
theorem flat : Flat s := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective s
  apply Flat.SpecMap_iff.mpr
  let := φ.hom.toAlgebra
  change Module.Flat k K
  infer_instance

/-- A field-spectrum map is surjective on its unique point. -/
theorem surjective : Surjective s := by
  constructor
  intro y
  exact ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩

/-- The actual field extension is a faithfully flat affine cover. -/
theorem effectiveEpi : EffectiveEpi s := by
  have : IsAffineHom s := isAffineHom_of_isAffine _
  have : Flat s := flat s
  have : Surjective s := surjective s
  infer_instance

/-- Base change along a field extension faithfully detects all scheme morphisms. -/
theorem pullback_faithful : (Over.pullback s).Faithful := by
  have : IsAffineHom s := isAffineHom_of_isAffine _
  have : Flat s := flat s
  have : Surjective s := surjective s
  have (X : Scheme.{u}) (g : X ⟶ Spec (.of k)) : Epi (pullback.fst g s) := by
    have : IsAffineHom (pullback.fst g s) := MorphismProperty.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback g s).flip (inferInstance : IsAffineHom s)
    have : Flat (pullback.fst g s) := MorphismProperty.of_isPullback (P := @Flat)
      (IsPullback.of_hasPullback g s).flip (inferInstance : Flat s)
    have : Surjective (pullback.fst g s) := MorphismProperty.of_isPullback (P := @Surjective)
      (IsPullback.of_hasPullback g s).flip (inferInstance : Surjective s)
    infer_instance
  infer_instance

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.Extension
