import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.SectionBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.EquivalentDimensions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalSectionsFunctor
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Extension Section Dimension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ExtensionSectionDimension

noncomputable section

/-! Actual global-section dimensions are preserved under arbitrary field extension. The full changed-field scalar action is supplied by the canonical flat section comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct
universe u

theorem schemeGlobalSections_finrank_eq_globalCoefficients
    {K : Type u} [CommRing K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (M : X.Modules) :
    Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M) =
      Module.finrank Γ(Spec (.of K), ⊤)
        ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor p.appTop.hom).obj M) := by
  let e : K ≃+* Γ(Spec (.of K), ⊤) :=
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm
  exact Scalar.EquivalentDimensions.restrictScalars_finrank_of_ringEquiv e
    ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor p.appTop.hom).obj M)

theorem fieldExtension_lineBundle_sections_finrank
    {K F : Type u} [Field K] [Field F] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [IsProper p]
    (φ : CommRingCat.of K ⟶ CommRingCat.of F) (L : Line.Bundles.LineBundle X) :
    Module.finrank F ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (pullback.snd p (Spec.map φ))).obj
        (L.pullback (pullback.fst p (Spec.map φ))).sheaf) =
      Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj L.sheaf) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have hp : IsSeparated (p ≫ terminal.from (Spec (.of K))) := inferInstance
  have : IsSeparated (terminal.from X) := (terminal.comp_from p) ▸ hp
  let : Field Γ(Spec (.of K), ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)).toField
  let : Field Γ(Spec (.of F), ⊤) :=
    ((Scheme.ΓSpecIso (.of F)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField F)).toField
  let : Algebra Γ(Spec (.of K), ⊤) Γ(Spec (.of F), ⊤) :=
    (Spec.map φ).appTop.hom.toAlgebra
  have : Module.Flat Γ(Spec (.of K), ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra (Spec.map φ)) := inferInstance
  let : Module Γ(Spec (.of F), ⊤)
      (TensorProduct Γ(Spec (.of K), ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra (Spec.map φ))
        ((Coefficient.ModulePresheaf.coefficientModulePresheaf p.appTop.hom L.sheaf).obj (.op ⊤))) := by
    change Module (Affine.TensorSectionComparison.morphismGlobalAlgebra (Spec.map φ))
      (TensorProduct Γ(Spec (.of K), ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra (Spec.map φ))
        ((Coefficient.ModulePresheaf.coefficientModulePresheaf p.appTop.hom L.sheaf).obj (.op ⊤)))
    infer_instance
  let e := Scalar.SectionBaseChange.flat_lineBundleGlobalSectionsEquiv (IsPullback.of_hasPullback p (Spec.map φ)) L
  rw [schemeGlobalSections_finrank_eq_globalCoefficients,
    schemeGlobalSections_finrank_eq_globalCoefficients]
  exact e.finrank_eq.symm.trans Module.finrank_baseChange

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ExtensionSectionDimension
