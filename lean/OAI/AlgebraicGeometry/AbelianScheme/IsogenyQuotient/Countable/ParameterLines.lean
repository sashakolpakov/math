import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.CoefficientFields
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.CoefficientLineDescent

/-! # Parameter Lines -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.ParameterLines.Construction

noncomputable section

/-! A line on a proper family defined over a countable subfield has an
actual line model after enlarging that subfield by countably many elements.
The enlargement stays inside the original geometric field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.CoefficientLineDescent

variable {k : Type} [Field k] [CharZero k] [IsAlgClosed k]

def subfieldParameter (F G : Subfield k) (hFG : F ≤ G) : Over (Spec (.of F)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (Subfield.inclusion hFG)))

def subfieldParameterRestriction (F G : Subfield k) (hFG : F ≤ G) :
    AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver F k ⟶ subfieldParameter F G hFG :=
  Over.homMk (Spec.map (CommRingCat.ofHom G.subtype)) (by
    change Spec.map (CommRingCat.ofHom G.subtype) ≫
      Spec.map (CommRingCat.ofHom (Subfield.inclusion hFG)) =
        Spec.map (CommRingCat.ofHom F.subtype)
    rw [← Spec.map_comp]
    rfl)

set_option backward.isDefEq.respectTransparency false in
theorem countable_parameter_line_model_exists
    (F : Subfield k) [Countable F] (X : Over (Spec (.of F))) [IsProper X.hom]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver F k ⊗ X).left) :
    ∃ G : Subfield k, Countable G ∧ IsAlgClosed G ∧
      ∃ hFG : F ≤ G, ∃ J : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (subfieldParameter F G hFG ⊗ X).left,
        Nonempty ((J.pullback (subfieldParameterRestriction F G hFG ▷ X).left).sheaf ≅ L.sheaf) := by
  obtain ⟨s, K, ⟨e⟩⟩ := AbelianModuli.ReferenceFamily.Finite.CoefficientLineDescent.exists_finite_coefficient_line_model F k X L
  obtain ⟨G, hG, ha, hFG, hsG⟩ := CoefficientFields.Construction.countable_subfield_finite_enlargement F s
  let R := AbelianModuli.ReferenceFamily.Finite.CoefficientDiagram.finiteCoefficientRing F k s
  have hRG (r : R) : (r : k) ∈ G := by
    exact Algebra.adjoin_induction (p := fun x _ => x ∈ G)
      (fun _ hx => hsG hx) (fun x => hFG x.property)
      (fun _ _ _ _ hx hy => G.add_mem hx hy)
      (fun _ _ _ _ hx hy => G.mul_mem hx hy) r.property
  let j : R →+* G := R.val.toRingHom.codRestrict G hRG
  let V := AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver F R
  let v : subfieldParameter F G hFG ⟶ V :=
    Over.homMk (Spec.map (CommRingCat.ofHom j)) (by
      change Spec.map (CommRingCat.ofHom j) ≫
        Spec.map (CommRingCat.ofHom (algebraMap F R)) =
          Spec.map (CommRingCat.ofHom (Subfield.inclusion hFG))
      rw [← Spec.map_comp]
      rfl)
  let q : AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver F k ⟶ V := AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecMap F R.val
  have hv : subfieldParameterRestriction F G hFG ≫ v = q := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom G.subtype) ≫ Spec.map (CommRingCat.ofHom j) =
      Spec.map (CommRingCat.ofHom R.val.toRingHom)
    rw [← Spec.map_comp]
    rfl
  let J := K.pullback (v ▷ X).left
  have hc : (subfieldParameterRestriction F G hFG ▷ X).left ≫ (v ▷ X).left =
      (AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.finiteCoefficientFamilyCone F k X).π.app (.op s) := by
    rw [← Over.comp_left, ← comp_whiskerRight, hv]
    rfl
  refine ⟨G, hG, ha, hFG, J, ?_⟩
  exact ⟨(Scheme.Modules.pullbackComp (subfieldParameterRestriction F G hFG ▷ X).left
    (v ▷ X).left).app K.sheaf ≪≫
      (Scheme.Modules.pullbackCongr hc).app K.sheaf ≪≫ e⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.ParameterLines.Construction
