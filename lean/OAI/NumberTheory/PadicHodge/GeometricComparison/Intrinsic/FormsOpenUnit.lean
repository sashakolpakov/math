import OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSheafification
import OAI.NumberTheory.PadicHodge.GeometricComparison.OpenForms
import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafificationUnit

/-! # Forms Open Unit -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.FormsOpenUnit.IntrinsicFormsOpenUnit

noncomputable section

/-! Invertibility of the native differential-form unit transports along the actual open restriction isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] {X Y : Over (Spec (CommRingCat.of R))}
  (f : Y ⟶ X) [IsOpenImmersion f.left] (n : ℕ) (U : Y.left.Opens)

theorem isIso_on_image
    (hU : IsIso ((toSheafify (Opens.grothendieckTopology Y.left)
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R Y n)).app (op U))) :
    IsIso ((toSheafify (Opens.grothendieckTopology X.left)
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n)).app (op (f.left ''ᵁ U))) :=
  OpenSheafification.OpenSheafificationUnit.isIso_on_image R f.left (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n) U
    (SheafificationUnit.SheafificationUnitTransfer.of_iso (Opens.grothendieckTopology Y.left)
      (OpenForms.OpenFormsSheaves.presheafIso f n) (op U) hU)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.FormsOpenUnit.IntrinsicFormsOpenUnit
