import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeFlat
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Integral First Three Sections -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.IntegralFirstThreeSections.SmoothIntegralFirstThreeSections

noncomputable section

/-! The actual affine-section algebras of a smooth model give prime-regular native zero- and one-forms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (.of R))) [Smooth X.hom]

theorem algebra_smooth (U : X.left.Opens) (hU : IsAffineOpen U) :
    Algebra.Smooth R ((OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).obj (op U)) := by
  change (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap R X U).Smooth
  exact (RingHom.Smooth.of_bijective
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.bijective).comp
      (X.hom.smooth_appLE (isAffineOpen_top _) hU (by simp))

theorem forms_flat (U : X.left.Opens) (hU : IsAffineOpen U) (n : ℕ) (hn : n ≤ 2) :
    Module.Flat R ((OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n).obj (op U)) := by
  let B := (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).obj (op U)
  let : Algebra.Smooth R B := algebra_smooth R X U hU
  exact IntegralFirst.ThreeFlat.IntegralFirstThreeFlat.flat R B n hn

theorem forms_regular (U : X.left.Opens) (hU : IsAffineOpen U)
    (n : ℕ) (hn : n ≤ 2) (r : R) (hr : IsRegular r) :
    IsSMulRegular ((OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n).obj (op U)) r := by
  let := forms_flat R X U hU n hn
  exact Module.Flat.isSMulRegular_of_isRegular hr

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.IntegralFirstThreeSections.SmoothIntegralFirstThreeSections
