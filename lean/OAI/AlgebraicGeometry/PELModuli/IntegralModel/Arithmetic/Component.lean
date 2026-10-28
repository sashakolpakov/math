import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LocalizedComponentComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComponentCoproduct

/-! # Component -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Component

noncomputable section

/-! The complete pointed component Albanese diagram has an actual smooth
proper arithmetic model with its original complex coproduct comparison. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem arithmetic_component_model_exists
    {K : Type} [Field K] [NumberField K] {T : Over (Spec (.of K))} {r : ℕ}
    (D : Components.ComponentAlbaneseData T r) (κ : K →+* ℂ) (e : (∐ D.S) ≅ T)
    (hS : ∀ i, Smooth (D.S i).hom ∧ IsProper (D.S i).hom ∧ GeometricallyConnected (D.S i).hom)
    (hA : ∀ i, Smooth (D.A i).X.hom ∧ IsProper (D.A i).X.hom ∧ GeometricallyConnected (D.A i).X.hom)
    (hAlb : ∀ i, D.IsComplexAlbanese (Spec.map (CommRingCat.ofHom κ)) i)
    (N : ℕ) (hN : N ≠ 0) :
    ∃ B : Base.ArithmeticBaseExtension K κ, IsUnit (N : B.R) ∧ N ∣ B.denominator ∧
      ∃ Q : Over B.base, Smooth Q.hom ∧ IsProper Q.hom ∧
        ∃ (V : Components.ComponentAlbaneseData Q r) (_e : (∐ V.S) ≅ Q)
          (_c : (Over.pullback B.complexPoint).obj Q ≅
            (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj T),
          ∀ i, Smooth (V.S i).hom ∧ IsProper (V.S i).hom ∧ GeometricallyConnected (V.S i).hom ∧
            Smooth (V.A i).X.hom ∧ IsProper (V.A i).X.hom ∧ GeometricallyConnected (V.A i).X.hom ∧
            V.IsComplexAlbanese B.complexPoint i := by
  obtain ⟨W, _, _⟩ := LocalizedComponentDiagramExists.localized_component_diagram_exists D κ hS hA N hN
  obtain ⟨B, hdiv, φ, hφ, ⟨j⟩⟩ := W.exists_baseChange_section N hN
  let C := W.base.compose B
  let S (i : Fin r) := (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj (W.source i)
  let Q : Over C.base := ∐ S
  let V : Components.ComponentAlbaneseData Q r := W.componentData B φ j Q
  have hg (i : Fin r) := W.componentData_geometry B φ j Q i
  obtain ⟨hsm, hp⟩ := ComponentCoproduct.component_coproduct_smooth_proper S (fun i => ⟨(hg i).1, (hg i).2.1⟩)
  refine ⟨C, C.divisor_isUnit N hdiv, hdiv, Q, hsm, hp, V, Iso.refl Q,
    W.componentCoproductComplexIso B φ hφ e, ?_⟩
  intro i
  exact ⟨(hg i).1, (hg i).2.1, (hg i).2.2.1, (hg i).2.2.2.1,
    (hg i).2.2.2.2.1, (hg i).2.2.2.2.2, W.componentData_isComplexAlbanese B φ j hφ Q i (hAlb i)⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Component
