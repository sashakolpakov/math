import OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationResidue

/-! # Closure Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClosureLocalization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual integral closure commutes with localization

The map is the literal inclusion of integral elements in the same field.
Its localization property applies to an affine chart and a stalk of the
original scheme, with the actual section-to-stalk scalar structures.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

section Algebra

variable (B R K : Type*) [CommRing B] [CommRing R] [Field K]
variable [Algebra B R] [Algebra B K] [Algebra R K] [IsScalarTower B R K]

def integralClosureInclusion : integralClosure B K →ₐ[B] integralClosure R K := by
  have h : integralClosure B K ≤ (integralClosure R K).restrictScalars B := fun _ hx => hx.tower_top
  exact Subalgebra.inclusion h

abbrev integralClosureInclusionAlgebra : Algebra (integralClosure B K) (integralClosure R K) :=
  (integralClosureInclusion B R K).toRingHom.toAlgebra

theorem integralClosure_isLocalization (M : Submonoid B) [IsLocalization M R] :
    letI := integralClosureInclusionAlgebra B R K
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure B K) M) (integralClosure R K) := by
  let := integralClosureInclusionAlgebra B R K
  let : IsScalarTower B (integralClosure B K) (integralClosure R K) :=
    IsScalarTower.of_algHom (integralClosureInclusion B R K)
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
variable (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] (x : U)

def normalizationStalkInclusion :
    integralClosure Γ(X, U) X.functionField →ₐ[Γ(X, U)] integralClosure (X.presheaf.stalk x) X.functionField := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  let := functionField_isScalarTower X U x
  exact integralClosureInclusion Γ(X, U) (X.presheaf.stalk x) X.functionField

theorem normalizationStalk_isLocalization :
    letI := (normalizationStalkInclusion X U x).toRingHom.toAlgebra
    IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure Γ(X, U) X.functionField) (hU.primeIdealOf x).asIdeal.primeCompl)
      (integralClosure (X.presheaf.stalk x) X.functionField) := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  let := functionField_isScalarTower X U x
  let := hU.isLocalization_stalk x
  exact integralClosure_isLocalization Γ(X, U) (X.presheaf.stalk x) X.functionField (hU.primeIdealOf x).asIdeal.primeCompl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClosureLocalization.BundleCycles
