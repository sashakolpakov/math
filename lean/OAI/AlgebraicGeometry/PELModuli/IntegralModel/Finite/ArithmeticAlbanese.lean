import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.AlbaneseExtension
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ArithmeticExtensions

/-! # Arithmetic Albanese -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ArithmeticAlbanese

noncomputable section

/-! Finitely many pointed arithmetic sources have actual Albanese
realizations over one common finite field, preserving their complex maps. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

structure FiniteArithmeticAlbaneseRealization
    {R I : Type} [Field R] [NumberField R] [Algebra R ℂ]
    (X : I → Over (Spec (.of R))) (x₀ : ∀ i, 𝟙_ (Over (Spec (.of R))) ⟶ X i)
    (A : I → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : ∀ i, (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj (X i) ⟶ (A i).toOver) where
  base : Base.ArithmeticBaseExtension R (algebraMap R ℂ)
  model : I → Quotients.FiniteDescent.AbelianQuotient.Construction.AbelianScheme (Spec (.of base.extension.carrier))
  map : ∀ i, (Over.pullback base.fieldExtension).obj (X i) ⟶ (model i).toOver
  sourceIso : ∀ i, (Over.pullback (Spec.map (CommRingCat.ofHom base.embedding))).obj
      ((Over.pullback base.fieldExtension).obj (X i)) ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj (X i)
  targetIso : ∀ i, (Over.pullback (Spec.map (CommRingCat.ofHom base.embedding))).obj (model i).toOver ≅ (A i).toOver
  groupComparison : ∀ i, IsMonHom (targetIso i).hom
  pointed : ∀ i, Section.Comparisons.mappedSection (Over.pullback base.fieldExtension) (x₀ i) ≫ map i = 1
  sourcePoint : ∀ i, Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom base.embedding)))
      (Section.Comparisons.mappedSection (Over.pullback base.fieldExtension) (x₀ i)) ≫ (sourceIso i).hom =
    Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) (x₀ i)
  comparison : ∀ i, (Over.pullback (Spec.map (CommRingCat.ofHom base.embedding))).map (map i) ≫ (targetIso i).hom =
    (sourceIso i).hom ≫ a i

theorem finite_arithmetic_albanese_realizations_exist
    {R I : Type} [Field R] [NumberField R] [Algebra R ℂ] [Finite I]
    (X : I → Over (Spec (.of R)))
    [∀ i, Smooth (X i).hom] [∀ i, IsProper (X i).hom] [∀ i, GeometricallyConnected (X i).hom]
    (x₀ : ∀ i, 𝟙_ (Over (Spec (.of R))) ⟶ X i)
    (P : ∀ i, Foundations.Scheme.SmoothProjective.ProjectivePresentation
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj (X i)).left
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj (X i)).hom)
    (N : ℕ) (hN : N ≠ 0) :
    ∃ (A : I → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
      (a : ∀ i, (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj (X i) ⟶ (A i).toOver)
      (D : FiniteArithmeticAlbaneseRealization X x₀ A a),
      (∀ i, Albanese.IsAlbaneseMap (AlbaneseArithmeticIsogeny.complexSourcePresentation (X i) (P i))
        (Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) (x₀ i)) (A i) (a i)) ∧
      D.base.denominator = N := by
  have h (i : I) := Arithmetic.AlbaneseExtension.arithmetic_albanese_realization_exists (X i) (x₀ i) (P i) N hN
  choose A a D hA _ _ using h
  obtain ⟨B, hB, φ, hφ, hφC⟩ :=
    Base.ArithmeticBaseExtension.finite_extensions_common (fun i => (D i).base) N hN
  let W (i : I) := (D i).extend B (φ i) (hφ i) (hφC i)
  let V : FiniteArithmeticAlbaneseRealization X x₀ A a := {
    base := B
    model := fun i => (W i).model
    map := fun i => (W i).map
    sourceIso := fun i => (W i).sourceIso
    targetIso := fun i => (W i).targetIso
    groupComparison := fun i => (W i).groupComparison
    pointed := fun i => (W i).pointed
    sourcePoint := fun i => (W i).sourcePoint
    comparison := fun i => (W i).comparison }
  exact ⟨A, a, V, hA, hB⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ArithmeticAlbanese
