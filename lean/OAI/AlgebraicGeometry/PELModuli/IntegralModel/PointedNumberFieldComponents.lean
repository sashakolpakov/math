import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComponentBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ArithmeticPoints
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Tower
import OAI.ArithmeticGeometry.Models.SpreadingOut.FiniteFieldComponents

/-! # Pointed Number Field Components -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedNumberFieldComponents

noncomputable section

/-! A smooth projective number-field scheme acquires an actual finite
decomposition into pointed geometrically connected components. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

theorem pointed_number_field_components_exist
    {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ)
    (X : Over (Spec (.of K))) [Smooth X.hom] [IsProper X.hom]
    (hproj : Components.RelativelyProjective X) (N : ℕ) (hN : N ≠ 0) :
    ∃ B : Base.ArithmeticBaseExtension K κ, B.denominator = N ∧
      ∃ (r : ℕ) (S : Fin r → Over (Spec (.of B.extension.carrier)))
        (_e : (∐ S) ≅ (Over.pullback B.fieldExtension).obj X)
        (_x₀ : ∀ i, 𝟙_ (Over (Spec (.of B.extension.carrier))) ⟶ S i),
        ∀ i, Smooth (S i).hom ∧ IsProper (S i).hom ∧
          GeometricallyConnected (S i).hom ∧ Components.RelativelyProjective (S i) := by
  obtain ⟨L, hL⟩ := ArithmeticGeometry.Models.SpreadingOut.FiniteFieldComponents.Construction.finite_smooth_proper_components_split_over_number_field
    K (fun _ : Unit => X) (fun _ => inferInstance) (fun _ => inferInstance)
  let B := Base.ArithmeticBaseExtension.ofFiniteExtension (⟨L.carrier⟩ : Arithmetic.Open.FiniteNumberFieldExtension K) κ N hN
  let X₁ := (Over.pullback B.fieldExtension).obj X
  have : Smooth X₁.hom := inferInstanceAs (Smooth (pullback.snd X.hom B.fieldExtension))
  have : IsProper X₁.hom := inferInstanceAs (IsProper (pullback.snd X.hom B.fieldExtension))
  have hsplit : ModelsHas.HasSplitGeometricComponents X₁ := hL ()
  obtain ⟨r, C, e, hC, hPC⟩ := SplitComponents.split_components_decomposition X₁ hsplit
  have hpr (i : Fin r) : Components.RelativelyProjective (C i) :=
    hPC (ComponentBaseChange.relativelyProjective_baseChange B.fieldExtension hproj) i
  have : ∀ i, LocallyOfFiniteType (C i).hom := by
    intro i
    have : Smooth (C i).hom := (hC i).1
    infer_instance
  have : ∀ i, Nonempty (C i).left := by
    intro i
    have : GeometricallyConnected (C i).hom := (hC i).2.2.1
    have : ConnectedSpace (C i).left :=
      GeometricallyConnected.connectedSpace_of_subsingleton (C i).hom
    infer_instance
  obtain ⟨D, hD, ⟨p⟩⟩ := Finite.ArithmeticPoints.finite_arithmetic_parameters_exist B.embedding C N hN
  let A := B.compose D
  let F := Over.pullback D.fieldExtension
  let S (i : Fin r) := F.obj (C i)
  let x₀ (i : Fin r) : 𝟙_ (Over (Spec (.of D.extension.carrier))) ⟶ S i :=
    Over.homMk (pullback.lift (p i).left (𝟙 _) ((p i).w.trans (Category.id_comp _).symm))
      (pullback.lift_snd _ _ _)
  let a : (∐ S) ≅ (Over.pullback A.fieldExtension).obj X :=
    ComponentBaseChange.baseChangeDecompositionIso D.fieldExtension C e ≪≫ (B.composeSourceNatIso D).app X
  refine ⟨A, hD, r, S, a, x₀, ?_⟩
  intro i
  have : Smooth (C i).hom := (hC i).1
  have : IsProper (C i).hom := (hC i).2.1
  have : GeometricallyConnected (C i).hom := (hC i).2.2.1
  exact ⟨inferInstanceAs (Smooth (pullback.snd (C i).hom D.fieldExtension)),
    inferInstanceAs (IsProper (pullback.snd (C i).hom D.fieldExtension)),
    inferInstanceAs (GeometricallyConnected (pullback.snd (C i).hom D.fieldExtension)),
    ComponentBaseChange.relativelyProjective_baseChange D.fieldExtension (hpr i)⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedNumberFieldComponents
