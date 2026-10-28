import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PushforwardSection
import OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.FormSectionUnit

/-! # Differential Symbol -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.DifferentialSymbol

noncomputable section

/-! Differential symbols with fixed parameters define a morphism on
the original principal-open diagram, with literal restriction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  (U : Y.left.Opens) (hU : IsAffineOpen U) (g : ℕ)
  (t : Fin g → Γ(X.left, f.left ⁻¹ᵁ U))

local instance sectionAlgebra (V : X.left.Opens) : Algebra R Γ(X.left, V) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X V

def generator : Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g, f.left ⁻¹ᵁ U) :=
  Integral.FormSectionUnit.unit R X g (f.left ⁻¹ᵁ U)
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(X.left, f.left ⁻¹ᵁ U) 1 t)

def map := PushforwardSection.map f.left U hU
  (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g) (generator R X Y f U g t)

theorem component (r : SectionPresheaf.Index U) (x : Γ(X.left, f.left ⁻¹ᵁ SectionPresheaf.openSubset U r)) :
    (DifferentialSymbol.map R X Y f U hU g t).app (op r) x =
      Integral.FormSectionUnit.unit R X g (f.left ⁻¹ᵁ SectionPresheaf.openSubset U r)
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(X.left, f.left ⁻¹ᵁ SectionPresheaf.openSubset U r) x
          (fun i => X.left.presheaf.map (PushforwardSection.sourceInclusion f.left U r).op (t i))) := by
  change x • (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g).presheaf.map
    (PushforwardSection.sourceInclusion f.left U r).op
      (Integral.FormSectionUnit.unit R X g (f.left ⁻¹ᵁ U)
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(X.left, f.left ⁻¹ᵁ U) 1 t)) = _
  erw [Integral.FormSectionUnit.restriction, AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol, map_one,
    ← (Integral.FormSectionUnit.unit R X g (f.left ⁻¹ᵁ SectionPresheaf.openSubset U r)).map_smul,
    ← AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one]
  rfl

theorem atOne (x : Γ(X.left, f.left ⁻¹ᵁ U)) :
    (DifferentialSymbol.map R X Y f U hU g t).app (op (AtOne.object U))
      (AtOne.equiv U (PushforwardSection.source f.left) x) =
      AtOne.equiv U
        (PushforwardSection.target f.left (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g))
        (Integral.FormSectionUnit.unit R X g (f.left ⁻¹ᵁ U)
          (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(X.left, f.left ⁻¹ᵁ U) x t)) := by
  have h := PushforwardSection.atOne f.left U hU
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g) (generator R X Y f U g t) x
  change (DifferentialSymbol.map R X Y f U hU g t).app (op (AtOne.object U))
      (AtOne.equiv U (PushforwardSection.source f.left) x) =
      AtOne.equiv U
        (PushforwardSection.target f.left (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g))
        (x • Integral.FormSectionUnit.unit R X g (f.left ⁻¹ᵁ U)
          (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(X.left, f.left ⁻¹ᵁ U) 1 t)) at h
  rw [← (Integral.FormSectionUnit.unit R X g (f.left ⁻¹ᵁ U)).map_smul,
    ← AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.DifferentialSymbol
