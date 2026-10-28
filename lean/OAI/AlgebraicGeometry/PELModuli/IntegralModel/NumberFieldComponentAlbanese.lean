import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedNumberFieldComponents
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.AlbaneseComponents
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter

/-! # Number Field Component Albanese -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.NumberFieldComponentAlbanese

noncomputable section

/-! Construct all pointed component Albanese maps over one finite field
extension of a smooth projective number-field scheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

theorem number_field_component_albanese_exists
    {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ)
    (X : Over (Spec (.of K))) [Smooth X.hom] [IsProper X.hom]
    (hproj : Components.RelativelyProjective X) (N : ℕ) (hN : N ≠ 0) :
    ∃ B : Base.ArithmeticBaseExtension K κ, B.denominator = N ∧
      ∃ (r : ℕ) (D : Components.ComponentAlbaneseData ((Over.pullback B.fieldExtension).obj X) r)
        (_e : (∐ D.S) ≅ (Over.pullback B.fieldExtension).obj X),
        ∀ i, Smooth (D.S i).hom ∧ IsProper (D.S i).hom ∧ Components.RelativelyProjective (D.S i) ∧
          GeometricallyConnected (D.S i).hom ∧ Smooth (D.A i).X.hom ∧
          IsProper (D.A i).X.hom ∧ GeometricallyConnected (D.A i).X.hom ∧
          D.IsComplexAlbanese (Spec.map (CommRingCat.ofHom B.embedding)) i := by
  obtain ⟨B, _, r, C, e, x₀, hC⟩ := PointedNumberFieldComponents.pointed_number_field_components_exist κ X hproj N hN
  let : Algebra B.extension.carrier ℂ := B.embedding.toAlgebra
  have : ∀ i, Smooth (C i).hom := fun i => (hC i).1
  have : ∀ i, IsProper (C i).hom := fun i => (hC i).2.1
  have : ∀ i, GeometricallyConnected (C i).hom := fun i => (hC i).2.2.1
  let b := Spec.map (CommRingCat.ofHom (algebraMap B.extension.carrier ℂ))
  let P (i : Fin r) : Foundations.Scheme.SmoothProjective.ProjectivePresentation
      ((Over.pullback b).obj (C i)).left ((Over.pullback b).obj (C i)).hom :=
    AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.nativeProjectivePresentation
      (Classical.choice (ComponentBaseChange.relativelyProjective_baseChange b (hC i).2.2.2))
  obtain ⟨A, a, D, hA, hD⟩ := Finite.ArithmeticAlbanese.finite_arithmetic_albanese_realizations_exist C x₀ P N hN
  let B' := B.compose D.base
  let T := (Over.pullback B'.fieldExtension).obj X
  let V : Components.ComponentAlbaneseData T r := D.componentData T
  let e' : (∐ V.S) ≅ T := ComponentBaseChange.baseChangeDecompositionIso D.base.fieldExtension C e ≪≫
    (B.composeSourceNatIso D.base).app X
  refine ⟨B', hD, r, V, e', ?_⟩
  intro i
  exact ⟨inferInstanceAs (Smooth (pullback.snd (C i).hom D.base.fieldExtension)),
    inferInstanceAs (IsProper (pullback.snd (C i).hom D.base.fieldExtension)),
    ComponentBaseChange.relativelyProjective_baseChange D.base.fieldExtension (hC i).2.2.2,
    inferInstanceAs (GeometricallyConnected (pullback.snd (C i).hom D.base.fieldExtension)),
    (D.model i).smooth, (D.model i).proper, (D.model i).connected,
    D.componentData_isComplexAlbanese T P hA i⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.NumberFieldComponentAlbanese
