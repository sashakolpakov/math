import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Charts
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizationStalks

/-! # Localization -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Localization

noncomputable section

/-! Normalizing the local ring of an affine chart is obtained by localizing
the chart's integral closure in the same function field. The ring map is
the literal inclusion of integral elements, with all scalar maps fixed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

section Algebra

variable (B R K : Type*) [CommRing B] [CommRing R] [Field K]
  [Algebra B R] [Algebra B K] [Algebra R K] [IsScalarTower B R K]

def closureInclusion : integralClosure B K →ₐ[B] integralClosure R K := by
  have h : integralClosure B K ≤ (integralClosure R K).restrictScalars B :=
    fun _ hx => hx.tower_top
  exact Subalgebra.inclusion h

abbrev closureAlgebra : Algebra (integralClosure B K) (integralClosure R K) :=
  (closureInclusion B R K).toRingHom.toAlgebra

theorem closure_isLocalization (M : Submonoid B) [IsLocalization M R] :
    letI := closureAlgebra B R K
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure B K) M)
      (integralClosure R K) := by
  let := closureAlgebra B R K
  let : IsScalarTower B (integralClosure B K) (integralClosure R K) :=
    IsScalarTower.of_algHom (closureInclusion B R K)
  let : IsScalarTower (integralClosure B K) (integralClosure R K) K :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsLocalization (Algebra.algebraMapSubmonoid K M) K :=
    IsLocalization.of_le_isUnit (fun x hx => by
      obtain ⟨m, hm, rfl⟩ := hx
      have h := (IsLocalization.map_units R (⟨m, hm⟩ : M)).map (algebraMap R K)
      change IsUnit (algebraMap B K m)
      simpa only [← IsScalarTower.algebraMap_apply] using h)
  exact IsLocalization.integralClosure M

end Algebra

universe u

variable (X : Scheme.{u}) [IsIntegral X]
  (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] (x : U)

/-- The actual integral-closure map from an affine normalization chart
to the normalization of one of the original scheme's stalks. -/
def normalizationStalkInclusion :
    integralClosure Γ(X, U) X.functionField →ₐ[Γ(X, U)]
      integralClosure (X.presheaf.stalk x) X.functionField := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  let := functionField_isScalarTower X U x
  exact closureInclusion Γ(X, U) (X.presheaf.stalk x) X.functionField

theorem normalizationStalk_isLocalization :
    letI := (normalizationStalkInclusion X U x).toRingHom.toAlgebra
    IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure Γ(X, U) X.functionField)
        (hU.primeIdealOf x).asIdeal.primeCompl)
      (integralClosure (X.presheaf.stalk x) X.functionField) := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  let := functionField_isScalarTower X U x
  let := hU.isLocalization_stalk x
  exact closure_isLocalization Γ(X, U) (X.presheaf.stalk x) X.functionField
    (hU.primeIdealOf x).asIdeal.primeCompl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Localization
