import OAI.AlgebraicGeometry.FormalGeometry.Completion.WeaklyEtaleFields
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Point -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Point.Construction

noncomputable section

/-!
# Completion: sections over a geometric point

A nonempty weakly étale scheme over an algebraically closed field has a
section. This is a geometric input toward exactness of evaluation at the
terminal object of the pro-étale site.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- A flat scheme diagonal for a field extension implies a flat multiplication
map on its tensor square. -/
theorem flat_lmul_of_flat_spec_diagonal
    [Flat (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap K L))))] :
    (Algebra.TensorProduct.lmul' K : L ⊗[K] L →ₐ[K] L).toRingHom.Flat := by
  apply (Flat.SpecMap_iff (f := CommRingCat.ofHom
    (Algebra.TensorProduct.lmul' K : L ⊗[K] L →ₐ[K] L).toRingHom)).mp
  have h := (inferInstance : Flat
    (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap K L)))))
  rw [diagonal_SpecMap] at h
  exact (MorphismProperty.cancel_right_of_respectsIso
    (@Flat : MorphismProperty Scheme.{u}) _ _).mp h

/-- Precomposing a morphism with flat diagonal by a monomorphism preserves
flatness of its diagonal. -/
theorem flat_diagonal_mono_comp {X Y Z : Scheme.{u}} (i : X ⟶ Y) (f : Y ⟶ Z)
    [Mono i] [Flat (pullback.diagonal f)] : Flat (pullback.diagonal (i ≫ f)) := by
  exact (MorphismProperty.diagonal (@Flat : MorphismProperty Scheme.{u})).comp_mem i f
    (inferInstanceAs (Flat (pullback.diagonal i)))
    (inferInstanceAs (Flat (pullback.diagonal f)))

/-- Every point of a weakly étale scheme over an algebraically closed field
gives a section of the structure morphism. -/
theorem weaklyEtale_exists_section [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [WeaklyEtale f] (x : X) :
    ∃ s : Spec (CommRingCat.of K) ⟶ X, s ≫ f = 𝟙 _ := by
  let i := X.fromSpecResidueField x
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ f)
  let : Algebra K (X.residueField x) := φ.hom.toAlgebra
  have hflat : Flat (pullback.diagonal (Spec.map φ)) := by
    rw [hφ]
    exact flat_diagonal_mono_comp i f
  have hb : Function.Bijective φ.hom :=
    WeaklyEtaleFields.Construction.algebraMap_bijective_of_flat_diagonal (flat_lmul_of_flat_spec_diagonal (K := K))
  have : IsIso φ := (ConcreteCategory.isIso_iff_bijective φ).mpr hb
  refine ⟨Spec.map (inv φ) ≫ i, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id]

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Point.Construction
