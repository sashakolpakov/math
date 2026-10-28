import OAI.AlgebraicGeometry.Quotients.FiniteDescent.DualEvaluationEq
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LineBundles

/-! # Dual Evaluation Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.DualEvaluationIs.Construction.DualEvaluation

noncomputable section

/-! Evaluation identifies a line bundle tensored with its dual with the structure sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable {X : Scheme.{u}}

local instance : ∀ V, IsMulCommutative (X.ringCatSheaf.obj.obj V) := fun V => by
  change IsMulCommutative (X.presheaf.obj V)
  exact IsMulCommutative.of_comm fun a b => mul_comm a b

/-- Evaluation is an isomorphism because it is bijective on every open inside
a trivializing cover. -/
theorem isIso (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) : IsIso (SheafCohomology.Projective.Evaluation.Scheme.Modules.ev L.sheaf) := by
  choose U hx e using L.locallyTrivial
  have hU : iSup U = ⊤ := by
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  have hw : SheafCohomology.Projective.OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj)
      (SheafCohomology.Projective.Evaluation.Scheme.Modules.evPre L.sheaf) := by
    apply SheafCohomology.Projective.Invertible.Scheme.Modules.sheafificationW_of_bijective_on_cover _ U hU
    intro x W hW
    let eU := SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso L.sheaf (U x)
      (SheafCohomology.Projective.Invertible.Scheme.Modules.restrictIsoOfPullbackIso L.sheaf (U x) (e x).some)
    exact DualEvaluationEq.Construction.DualEvaluationFrames.bijective L.sheaf W
      (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf L.sheaf (U x) eU
        (Over.mk (homOfLE hW)))
  have hi : IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (SheafCohomology.Projective.Evaluation.Scheme.Modules.evPre L.sheaf)) := hw
  rw [SheafCohomology.Projective.Evaluation.Scheme.Modules.ev_eq_sheafification_map]
  exact IsIso.comp_isIso' hi (SheafCohomology.Projective.Invertible.Scheme.Modules.sheafifyValIso (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)).isIso_hom

/-- The canonical evaluation isomorphism `L ⊗ L∨ ≅ O`. -/
def iso (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    (L.tensor (DualLine.Construction.DualLineBundle.dual L)).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X :=
  @asIso _ _ _ _ (SheafCohomology.Projective.Evaluation.Scheme.Modules.ev L.sheaf) (isIso L)

theorem tensorClass_dual (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorClass q (DualLine.Construction.DualLineBundle.dualClass q) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass X := by
  induction q using Quotient.inductionOn with
  | h L => exact Quotient.sound ⟨iso L⟩

theorem dual_tensorClass (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorClass (DualLine.Construction.DualLineBundle.dualClass q) q = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass X :=
  (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorClass_comm _ _).trans (tensorClass_dual q)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.DualEvaluationIs.Construction.DualEvaluation
