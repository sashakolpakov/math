import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperFunctionsEq
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Proper Integral -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperIntegral.Construction.ProperIntegralFunctions

/-! Global functions on a proper scheme are integral over an affine base.
This uses properness of the affinization map and descent of universal
closedness, without a cohomology finiteness hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

noncomputable def scalarMap {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) :
    R ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso R).inv ≫ f.appTop

theorem factor {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) :
    X.toSpecΓ ≫ Spec.map (scalarMap f) = f := by
  simp only [scalarMap, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem isProper_toSpecΓ {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) [IsProper f] : IsProper X.toSpecΓ := by
  have : IsProper (X.toSpecΓ ≫ Spec.map (scalarMap f)) := by
    rw [factor]
    infer_instance
  exact IsProper.of_comp X.toSpecΓ (Spec.map (scalarMap f))

theorem isIntegral {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) [IsProper f] : (scalarMap f).hom.IsIntegral := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := isProper_toSpecΓ f
  have : Surjective X.toSpecΓ := inferInstance
  have : UniversallyClosed (X.toSpecΓ ≫ Spec.map (scalarMap f)) := by
    rw [factor]
    infer_instance
  have : UniversallyClosed (Spec.map (scalarMap f)) :=
    UniversallyClosed.of_comp_surjective X.toSpecΓ (Spec.map (scalarMap f))
  exact IsIntegralHom.SpecMap_iff.mp
    (IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩)

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperIntegral.Construction.ProperIntegralFunctions
