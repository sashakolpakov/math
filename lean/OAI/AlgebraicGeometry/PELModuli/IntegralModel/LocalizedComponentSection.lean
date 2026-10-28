import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LocalizedComponentDiagramExists
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.ArithmeticIsomorphisms

/-! # Localized Component Section -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The modeled base point becomes an actual arithmetic section after
a constructed base change, using its exact complex unit comparison. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

theorem LocalizedComponentDiagramExists.LocalizedComponentDiagram.exists_baseChange_section
    {K : Type} [Field K] [NumberField K] {T : Over (Spec (.of K))} {r : ℕ}
    {D : Components.ComponentAlbaneseData T r} {κ : K →+* ℂ} (W : LocalizedComponentDiagramExists.LocalizedComponentDiagram D κ)
    (N : ℕ) (hN : N ≠ 0) :
    ∃ B : Base.ArithmeticBaseExtension W.base.extension.carrier W.base.embedding,
      N ∣ B.denominator ∧ ∃ φ : W.base.R →+* B.R,
        B.toField.comp φ = (algebraMap W.base.extension.carrier B.extension.carrier).comp W.base.toField ∧
        Nonempty (𝟙_ (Over B.base) ⟶
          (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj W.unitModel) := by
  let C := W.base
  let : Algebra C.R ℂ := (C.embedding.comp C.toField).toAlgebra
  let b := Spec.map (CommRingCat.ofHom (algebraMap C.R ℂ))
  have hb : b = C.complexPoint :=
    Spec.map_comp (CommRingCat.ofHom C.toField) (CommRingCat.ofHom C.embedding)
  let F := Over.pullback C.complexPoint
  let G := Over.pullback (Spec.map (CommRingCat.ofHom κ))
  let U : Over C.base := 𝟙_ (Over C.base)
  have : IsIso U.hom := inferInstanceAs (IsIso (𝟙 C.base))
  let e : (Over.pullback b).obj W.unitModel ≅ (Over.pullback b).obj U := by
    rw [hb]
    exact W.unitIso ≪≫ (Functor.Monoidal.εIso G).symm ≪≫ Functor.Monoidal.εIso F
  have : Smooth W.unitModel.hom := W.unitGeometry.1
  have : IsProper W.unitModel.hom := W.unitGeometry.2
  obtain ⟨B, hdiv, φ, hφ, ⟨a⟩⟩ := Fixed.ArithmeticIsomorphisms.arithmetic_fixed_isomorphism_exists C rfl W.unitModel U
    ⟨inferInstance, inferInstance, inferInstance⟩ ⟨inferInstance, inferInstance, inferInstance⟩ e N hN
  let H := Over.pullback (Spec.map (CommRingCat.ofHom φ))
  exact ⟨B, hdiv, φ, hφ, ⟨(Functor.Monoidal.εIso H).hom ≫ a.inv⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
