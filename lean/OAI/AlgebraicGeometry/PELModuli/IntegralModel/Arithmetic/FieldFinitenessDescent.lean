import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.FieldExtensionReduced
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.CoverType
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Field Finiteness Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Finiteness of the actual reference scheme descends through the
specified finite number-field extension. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : Base.ArithmeticBaseExtension K κ)

theorem Base.ArithmeticBaseExtension.fieldExtension_finiteness_descent (X : Over (Spec (.of K)))
    (hft : LocallyOfFiniteType ((Over.pullback B.fieldExtension).obj X).hom)
    (hqc : QuasiCompact ((Over.pullback B.fieldExtension).obj X).hom) :
    LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom ∧ IsNoetherian X.left := by
  have := (B.fieldExtension_finite_etale).1
  have := (B.fieldExtension_finite_etale).2
  have : Surjective B.fieldExtension :=
    ⟨fun x => ⟨(⊥ : PrimeSpectrum B.extension.carrier), Subsingleton.elim _ x⟩⟩
  have : LocallyOfFiniteType X.hom := MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (IsPullback.of_hasPullback X.hom B.fieldExtension).flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hft
  have : QuasiCompact (pullback.snd X.hom B.fieldExtension) := hqc
  have : QuasiCompact (pullback.fst X.hom B.fieldExtension ≫ X.hom) := by
    rw [pullback.condition]
    infer_instance
  have : QuasiCompact X.hom := Finite.CoverType.quasiCompact_of_surjective_comp
    (pullback.fst X.hom B.fieldExtension) X.hom
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  exact ⟨inferInstance, inferInstance, ⟨⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
