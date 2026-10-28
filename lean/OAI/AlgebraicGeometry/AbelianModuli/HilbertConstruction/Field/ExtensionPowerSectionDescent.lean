import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.FieldSectionSpanning
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionSpanDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FieldExtensionReflection

/-! # Extension Power Section Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Ampleness after a field extension yields pointwise nonvanishing sections of positive powers downstairs on a proper scheme. The spanning hypothesis is supplied by flat section base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem Line.Bundles.LineBundle.pointwise_power_sections_of_ample_fieldExtension
    {K F : Type u} [Field K] [Field F] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [IsProper p] (φ : CommRingCat.of K ⟶ CommRingCat.of F)
    (L : Line.Bundles.LineBundle X) (hL : (L.pullback (pullback.fst p (Spec.map φ))).IsAmple) :
    ∀ x : X, ∃ (n : ℕ) (_ : 0 < n) (s : Line.Bundles.structureModule X ⟶ (L.tensorPower n).sheaf),
      x ∈ Ample.LineBundles.sectionNonvanishing s := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have hp : IsSeparated (p ≫ terminal.from (Spec (.of K))) := inferInstance
  have : IsSeparated (terminal.from X) := (terminal.comp_from p) ▸ hp
  have : Surjective (Spec.map φ) := Smooth.FieldExtensionReflection.fieldSpecMap_surjective φ
  let := ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)).toField
  have : Module.Flat Γ(Spec (.of K), ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra (Spec.map φ)) := inferInstance
  apply L.pointwise_power_sections_of_surjective_spanning_pullback
    (pullback.fst p (Spec.map φ)) (pullback.snd p (Spec.map φ)) hL
  intro n t
  exact HilbertConstruction.Flat.FieldSectionSpanning.flat_fieldPullback_sections_spanned (IsPullback.of_hasPullback p (Spec.map φ)) (L.tensorPower n) t

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
