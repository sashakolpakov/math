import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComponentPrecomparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComponentIdentification

/-! # Component Albanese Existence -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComponentAlbaneseExistence

noncomputable section

/-! Construct the complete arithmetic component Albanese data on the
actual base change of any specified smooth projective arithmetic scheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem arithmetic_component_albanese_exists
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : Base.ArithmeticBaseExtension K κ) (Q : Over B.base) [Smooth Q.hom] [IsProper Q.hom]
    (hQ : Components.RelativelyProjective Q) :
    ∃ E : Base.ArithmeticBaseExtension B.extension.carrier B.embedding,
      ∃ φ : B.R →+* E.R,
        E.toField.comp φ = (algebraMap B.extension.carrier E.extension.carrier).comp B.toField ∧
        ∃ (r : ℕ) (D : Components.ComponentAlbaneseData ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Q) r)
          (_e : (∐ D.S) ≅ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Q),
          ∀ i, Smooth (D.S i).hom ∧ IsProper (D.S i).hom ∧ Components.RelativelyProjective (D.S i) ∧
            GeometricallyConnected (D.S i).hom ∧ Smooth (D.A i).X.hom ∧ IsProper (D.A i).X.hom ∧
            GeometricallyConnected (D.A i).X.hom ∧ D.IsComplexAlbanese (B.compose E).complexPoint i := by
  obtain ⟨E, φ, hφ, W, hsm, hp, r, V, e, ec, hV⟩ := ComponentPrecomparison.arithmetic_component_precomparison_exists B Q hQ
  let C := B.compose E
  let g := Spec.map (CommRingCat.ofHom φ)
  let Q₁ := (Over.pullback g).obj Q
  have : Smooth Q₁.hom := inferInstanceAs (Smooth (pullback.snd Q.hom g))
  have : IsProper Q₁.hom := inferInstanceAs (IsProper (pullback.snd Q.hom g))
  have : Smooth W.hom := hsm
  have : IsProper W.hom := hp
  have hs : ∀ i, Smooth (V.S i).hom ∧ IsProper (V.S i).hom ∧ GeometricallyConnected (V.S i).hom :=
    fun i => ⟨(hV i).1, (hV i).2.1, (hV i).2.2.1⟩
  have ha : ∀ i, Smooth (V.A i).X.hom ∧ IsProper (V.A i).X.hom ∧ GeometricallyConnected (V.A i).X.hom :=
    fun i => ⟨(hV i).2.2.2.1, (hV i).2.2.2.2.1, (hV i).2.2.2.2.2.1⟩
  obtain ⟨J, _, ψ, hψ, D, eD, hD⟩ := ComponentIdentification.identify_arithmetic_component_model C Q₁ W
    (ComponentBaseChange.relativelyProjective_baseChange g hQ) V e ec hs ha (fun i => (hV i).2.2.2.2.2.2)
    C.denominator C.denominator_ne_zero
  let L := E.compose J
  let ρ : B.R →+* L.R := ψ.comp φ
  have hψ' : J.toField.comp ψ = (algebraMap E.extension.carrier J.extension.carrier).comp E.toField := hψ
  have hρ : L.toField.comp ρ = (algebraMap B.extension.carrier L.extension.carrier).comp B.toField := by
    change J.toField.comp (ψ.comp φ) =
      ((algebraMap E.extension.carrier J.extension.carrier).comp
        (algebraMap B.extension.carrier E.extension.carrier)).comp B.toField
    rw [← RingHom.comp_assoc, hψ', RingHom.comp_assoc, hφ, ← RingHom.comp_assoc]
  let a := Group.BaseChangeComparisons.GroupBaseChange.iteratedIso Q g (Spec.map (CommRingCat.ofHom ψ))
    (Spec.map (CommRingCat.ofHom ρ))
    (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ)).symm
  let V' := D.retarget ((Over.pullback (Spec.map (CommRingCat.ofHom ρ))).obj Q)
  exact ⟨L, ρ, hρ, r, V', eD ≪≫ a, hD⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComponentAlbaneseExistence
