import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComponentAlbaneseBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComponentCoproduct
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.ArithmeticIsomorphisms

/-! # Component Identification -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComponentIdentification

noncomputable section

/-! Identify a constructed component model with the specified arithmetic
parameter after base change, inheriting actual projective component embeddings. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem identify_arithmetic_component_model
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : Base.ArithmeticBaseExtension K κ) (Q W : Over B.base)
    [Smooth Q.hom] [IsProper Q.hom] [Smooth W.hom] [IsProper W.hom]
    (hQ : Components.RelativelyProjective Q) {r : ℕ} (V : Components.ComponentAlbaneseData W r) (e : (∐ V.S) ≅ W)
    (ec : (Over.pullback B.complexPoint).obj W ≅ (Over.pullback B.complexPoint).obj Q)
    (hS : ∀ i, Smooth (V.S i).hom ∧ IsProper (V.S i).hom ∧ GeometricallyConnected (V.S i).hom)
    (hA : ∀ i, Smooth (V.A i).X.hom ∧ IsProper (V.A i).X.hom ∧ GeometricallyConnected (V.A i).X.hom)
    (hAlb : ∀ i, V.IsComplexAlbanese B.complexPoint i) (N : ℕ) (hN : N ≠ 0) :
    ∃ E : Base.ArithmeticBaseExtension B.extension.carrier B.embedding,
      N ∣ E.denominator ∧ ∃ φ : B.R →+* E.R,
        E.toField.comp φ = (algebraMap B.extension.carrier E.extension.carrier).comp B.toField ∧
        ∃ (D : Components.ComponentAlbaneseData ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Q) r)
          (_e : (∐ D.S) ≅ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Q),
          ∀ i, Smooth (D.S i).hom ∧ IsProper (D.S i).hom ∧ Components.RelativelyProjective (D.S i) ∧
            GeometricallyConnected (D.S i).hom ∧ Smooth (D.A i).X.hom ∧ IsProper (D.A i).X.hom ∧
            GeometricallyConnected (D.A i).X.hom ∧ D.IsComplexAlbanese (B.compose E).complexPoint i := by
  let : Algebra B.R ℂ := (B.embedding.comp B.toField).toAlgebra
  let b := Spec.map (CommRingCat.ofHom (algebraMap B.R ℂ))
  have hb : b = B.complexPoint :=
    Spec.map_comp (CommRingCat.ofHom B.toField) (CommRingCat.ofHom B.embedding)
  let ec' : (Over.pullback b).obj W ≅ (Over.pullback b).obj Q := by rw [hb]; exact ec
  obtain ⟨E, hdiv, φ, hφ, ⟨a⟩⟩ := Fixed.ArithmeticIsomorphisms.arithmetic_fixed_isomorphism_exists B rfl W Q
    ⟨inferInstance, inferInstance, inferInstance⟩ ⟨inferInstance, inferInstance, inferInstance⟩ ec' N hN
  let g := Spec.map (CommRingCat.ofHom φ)
  let F := Over.pullback g
  let D := (V.baseChange g).retarget (F.obj Q)
  let e' : (∐ D.S) ≅ F.obj Q := ComponentBaseChange.baseChangeDecompositionIso g V.S e ≪≫ a
  have hproj : Components.RelativelyProjective (F.obj Q) := ComponentBaseChange.relativelyProjective_baseChange g hQ
  refine ⟨E, hdiv, φ, hφ, D, e', ?_⟩
  intro i
  have hg := V.baseChange_geometry g hS hA i
  have ha : D.IsComplexAlbanese (B.compose E).complexPoint i :=
    V.baseChange_isComplexAlbanese g B.complexPoint (B.compose E).complexPoint
      (B.tower_coefficient_complexPoint E φ hφ) i (hAlb i)
  exact ⟨hg.1, hg.2.1, ComponentCoproduct.projective_components_of_decomposition D.S e' hproj i,
    hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2, ha⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComponentIdentification
