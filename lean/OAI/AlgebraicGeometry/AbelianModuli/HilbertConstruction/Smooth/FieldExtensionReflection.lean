import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FpqcReflection

/-! # Field Extension Reflection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FieldExtensionReflection

noncomputable section

/-! Smoothness of schemes over fields is reflected by arbitrary field extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem fieldSpecMap_flat {K L : Type u} [Field K] [Field L] (φ : CommRingCat.of K ⟶ CommRingCat.of L) :
    Flat (Spec.map φ) := by
  let : Algebra K L := φ.hom.toAlgebra
  apply (HasRingHomProperty.Spec_iff (P := @Flat)).mpr
  exact (RingHom.flat_algebraMap_iff).mpr (inferInstanceAs (Module.Flat K L))

theorem fieldSpecMap_surjective {K L : Type u} [Field K] [Field L] (φ : CommRingCat.of K ⟶ CommRingCat.of L) :
    Surjective (Spec.map φ) := by
  constructor
  intro x
  exact ⟨(⊥ : PrimeSpectrum L), Subsingleton.elim _ _⟩

theorem smooth_of_isPullback_over_fields
    {K L : Type u} [Field K] [Field L] (φ : CommRingCat.of K ⟶ CommRingCat.of L)
    {X Y : Scheme.{u}} (q : Y ⟶ X) (p : Y ⟶ Spec (.of L)) (f : X ⟶ Spec (.of K))
    (h : IsPullback q p f (Spec.map φ)) [Smooth p] : Smooth f := by
  have : Flat (Spec.map φ) := fieldSpecMap_flat φ
  have : Surjective (Spec.map φ) := fieldSpecMap_surjective φ
  exact FpqcReflection.smooth_of_isPullback_fpqc q p f (Spec.map φ) h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FieldExtensionReflection
