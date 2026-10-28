import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionGlobal

/-! # Adjunction Global Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionGlobalCoordinates

noncomputable section

/-! The original global projective adjunction has the prescribed
local coordinate map on every genuine adjunction chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
attribute [local irreducible] AdjunctionCharts.Data.sectionIso LocalAdjunction.sectionIso
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ IntrinsicOverlap.Intrinsic.model R n)
  [IsClosedImmersion f.left] [Smooth X.hom] [IsProper X.hom]
  (g : ℕ) [SmoothOfRelativeDimension g X.hom]
  (j : Fin (n + 1)) (B : ℕ) (hB : n + 1 ≤ B) (hg : g ≤ n)
  (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U)
  (D : AdjunctionCharts.Data X f g U hU) (i : Fin (n + 1)) (hUi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)

theorem data_app (x : Γ(AdjunctionGluing.sourceSheaf X f g j B, U)) :
    (AdjunctionGlobal.iso X f g j B hB hg).hom.app U x = (D.sectionIso X f g i hUi j B hB hg).hom x := by
  let C : AdjunctionCharts.Chart X f g U :=
    { affine := hU, coordinate := i, le_coordinate := hUi, description := Sum.inr D }
  have h := AdjunctionGlobal.iso_app X f g j B hB hg hU (show AdjunctionCharts.Good X f g U from ⟨C⟩) x
  rw [ChartIndependence.AdjunctionCharts.chosenSectionIso_eq X f g _ C j B hB hg] at h
  dsimp only [AdjunctionCharts.Chart.sectionIso, C] at h
  exact h

theorem data_sections :
    (Affine.ModuleExactSections.sections U).map (AdjunctionGlobal.iso X f g j B hB hg).hom =
      (D.sectionIso X f g i hUi j B hB hg).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact data_app X f g j B hB hg U hU D i hUi x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionGlobalCoordinates
