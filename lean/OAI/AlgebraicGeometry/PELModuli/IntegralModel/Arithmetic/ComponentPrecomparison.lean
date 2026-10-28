import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Component
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.NumberFieldComponentAlbanese
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.TowerDenominatorMap

/-! # Component Precomparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComponentPrecomparison

noncomputable section

/-! Construct an arithmetic component model with the complex fiber of
the specified smooth projective arithmetic parameter and an actual base map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem arithmetic_component_precomparison_exists
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : Base.ArithmeticBaseExtension K κ) (Q : Over B.base) [Smooth Q.hom] [IsProper Q.hom]
    (hQ : Components.RelativelyProjective Q) :
    ∃ E : Base.ArithmeticBaseExtension B.extension.carrier B.embedding,
      ∃ φ : B.R →+* E.R,
        E.toField.comp φ = (algebraMap B.extension.carrier E.extension.carrier).comp B.toField ∧
        ∃ W : Over (B.compose E).base, Smooth W.hom ∧ IsProper W.hom ∧
          ∃ (r : ℕ) (V : Components.ComponentAlbaneseData W r) (_e : (∐ V.S) ≅ W)
            (_c : (Over.pullback (B.compose E).complexPoint).obj W ≅
              (Over.pullback (B.compose E).complexPoint).obj
                ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Q)),
            ∀ i, Smooth (V.S i).hom ∧ IsProper (V.S i).hom ∧ GeometricallyConnected (V.S i).hom ∧
              Smooth (V.A i).X.hom ∧ IsProper (V.A i).X.hom ∧ GeometricallyConnected (V.A i).X.hom ∧
              V.IsComplexAlbanese (B.compose E).complexPoint i := by
  let X := (Over.pullback B.generic).obj Q
  have : Smooth X.hom := inferInstanceAs (Smooth (pullback.snd Q.hom B.generic))
  have : IsProper X.hom := inferInstanceAs (IsProper (pullback.snd Q.hom B.generic))
  obtain ⟨L, _, r, D, eD, hD⟩ := NumberFieldComponentAlbanese.number_field_component_albanese_exists B.embedding X
    (ComponentBaseChange.relativelyProjective_baseChange B.generic hQ) B.denominator B.denominator_ne_zero
  have hs : ∀ i, Smooth (D.S i).hom ∧ IsProper (D.S i).hom ∧ GeometricallyConnected (D.S i).hom := by
    intro i
    obtain ⟨a, b, _, c, _, _, _, _⟩ := hD i
    exact ⟨a, b, c⟩
  have ha : ∀ i, Smooth (D.A i).X.hom ∧ IsProper (D.A i).X.hom ∧ GeometricallyConnected (D.A i).X.hom := by
    intro i
    obtain ⟨_, _, _, _, a, b, c, _⟩ := hD i
    exact ⟨a, b, c⟩
  have hal : ∀ i, D.IsComplexAlbanese (Spec.map (CommRingCat.ofHom L.embedding)) i := by
    intro i
    exact (hD i).2.2.2.2.2.2.2
  obtain ⟨J, _, hdiv, W, hsm, hp, V, eV, ec, hV⟩ :=
    Component.arithmetic_component_model_exists D L.embedding eD hs ha hal B.denominator B.denominator_ne_zero
  let E := L.compose J
  let C := B.compose E
  obtain ⟨φ, hφ⟩ := B.exists_tower_denominator_map E B.denominator B.denominator_ne_zero hdiv
  let g := Spec.map (CommRingCat.ofHom φ)
  let a := Group.BaseChangeComparisons.GroupBaseChange.iteratedIso Q B.generic (Spec.map (CommRingCat.ofHom B.embedding))
    B.complexPoint rfl
  let c := Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso g C.complexPoint B.complexPoint
    (B.tower_coefficient_complexPoint E φ hφ)
  let e : (Over.pullback C.complexPoint).obj W ≅
      (Over.pullback C.complexPoint).obj ((Over.pullback g).obj Q) :=
    ec ≪≫ Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso L X ≪≫ a ≪≫ (c.app Q).symm
  exact ⟨E, φ, hφ, W, hsm, hp, r, V, eV, e, hV⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComponentPrecomparison
