import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SelectedSymbolRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryFractionRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryFormScalars

/-! # Selected Fraction Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SelectedFractionRestriction

noncomputable section

section

/-! The selected differential symbol restricts to the same literal
native fraction, with the original arbitrary Witt coefficient. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (Z : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  (π : X ⟶ Z) (U : Z.left.Opens) (hU : IsAffineOpen U)
  (V : X.left.affineOpens) (hVU : V.val ≤ π.left ⁻¹ᵁ U)
  (g : ℕ) (t : Fin g → Γ(Z.left,U))

local instance ambientAlgebra : Algebra (Truncated.Witt.Ring p k n) Γ(Z.left,U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (Truncated.Witt.Ring p k n) Z U
local instance sourceAlgebra (W : X.left.Opens) :
    Algebra (Truncated.Witt.Ring p k n) Γ(X.left,W) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (Truncated.Witt.Ring p k n) X W

abbrev generator := Principal.DifferentialSymbol.generator
  (Truncated.Witt.Ring p k n) X Z π U g
  (Principal.DifferentialSymbolRestriction.sourceParameters
    (Truncated.Witt.Ring p k n) X Z π U t)

variable (z : Γ(X.left,π.left ⁻¹ᵁ U))

def selectedSection :=
  Integral.FormSectionUnit.unit (Truncated.Witt.Ring p k n) X g (π.left ⁻¹ᵁ U)
    (z • AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol (Truncated.Witt.Ring p k n) Γ(X.left,π.left ⁻¹ᵁ U) 1
      (Principal.DifferentialSymbolRestriction.sourceParameters
        (Truncated.Witt.Ring p k n) X Z π U t))

omit [Fintype k] [CharP k p] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] in
theorem selectedSection_eq : selectedSection p k n X Z π U g t z =
    z • generator p k n X Z π U g t :=
  (Integral.FormSectionUnit.unit (Truncated.Witt.Ring p k n) X g (π.left ⁻¹ᵁ U)).map_smul z _

def sourceClass (r : WittVector p k) :=
  Principal.SelectedSymbolRestriction.sourceClass π.left U hU
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g)
    (selectedSection p k n X Z π U g t z) t
    (Truncated.Witt.Ring p k n) (Truncated.Witt.quotient p k n r)

variable {κ : Type} [CommRing κ] (η : Γ(X.left,V.val) →+* κ)
  (hk : Koszul.OrientedTopCohomology.ideal Γ(X.left,V.val)
    (PrincipalResidue.ResidueRestriction.parameters π.left U V.val hVU t) = RingHom.ker η)
  (hz : η (X.left.presheaf.map (homOfLE hVU).op z) = 1)

include hk hz in
omit [IsSeparated Y.hom] in
omit [IsProper X.hom] [X.left.IsSeparated] in
theorem restriction (r : WittVector p k) :
    homologyMap (PrincipalSource.OpenTopClass.complexMap π.left U hU V.val V.property hVU
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g) t) g
      (sourceClass p k n X Z π U hU g t z r) =
    OrdinaryFractionRestriction.Ordinary.targetClass p k n X Y f hp Z π U V hVU g t r := by
  dsimp only [sourceClass]
  rw [selectedSection_eq]
  exact (Principal.SelectedSymbolRestriction.restriction π.left U hU V.val V.property hVU
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g)
    (generator p k n X Z π U g t) t (Truncated.Witt.Ring p k n) η hk z hz
    (Truncated.Witt.quotient p k n r)).trans
      (OrdinaryFractionRestriction.Ordinary.topClass p k n X Y f hp Z π U hU V hVU g t r)

variable (Q : Type) [CommRing Q] [Algebra (Truncated.Witt.Ring p k n) Q]
  [Algebra Q Γ(X.left,π.left ⁻¹ᵁ U)]
  [IsScalarTower (Truncated.Witt.Ring p k n) Q Γ(X.left,π.left ⁻¹ᵁ U)]
  (τ : Fin g → Q)
  (hτ : ∀ j, algebraMap Q Γ(X.left,π.left ⁻¹ᵁ U) (τ j) = π.left.app U (t j))

include hk hz hτ in
omit [IsSeparated Y.hom] in
omit [IsProper X.hom] [X.left.IsSeparated] in
theorem mapped_restriction (r : WittVector p k) :
    homologyMap (PrincipalSource.OpenTopClass.complexMap π.left U hU V.val V.property hVU
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g) t) g
      (Principal.SelectedSymbolRestriction.sourceClass π.left U hU
        (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g)
        (Integral.FormSectionUnit.unit (Truncated.Witt.Ring p k n) X g (π.left ⁻¹ᵁ U)
          (z • OrdinaryFormScalars.Ordinary.map (Truncated.Witt.Ring p k n) Q
            Γ(X.left,π.left ⁻¹ᵁ U) g
            (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol (Truncated.Witt.Ring p k n) Q 1 τ))) t
        (Truncated.Witt.Ring p k n) (Truncated.Witt.quotient p k n r)) =
    OrdinaryFractionRestriction.Ordinary.targetClass p k n X Y f hp Z π U V hVU g t r := by
  rw [OrdinaryFormScalars.Ordinary.map_symbol, map_one]
  have ht : (fun j => algebraMap Q Γ(X.left,π.left ⁻¹ᵁ U) (τ j)) =
      Principal.DifferentialSymbolRestriction.sourceParameters
        (Truncated.Witt.Ring p k n) X Z π U t := funext hτ
  rw [ht]
  exact restriction p k n X Y f hp Z π U hU V hVU g t z η hk hz r

end

/-! The finite pullback numerator is the literal selected differential
section for the composite parameters. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  (X Z : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))) (π : X ⟶ Z)
  (U : Z.left.Opens) (g : ℕ) (t : Fin g → Γ(Z.left,U))
  (z : Γ(X.left,π.left ⁻¹ᵁ U))
local instance sourceBase : Algebra (Truncated.Witt.Ring p k n) Γ(X.left,π.left ⁻¹ᵁ U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (Truncated.Witt.Ring p k n) X (π.left ⁻¹ᵁ U)
variable (Q : Type) [CommRing Q] [Algebra (Truncated.Witt.Ring p k n) Q]
  [Algebra Q Γ(X.left,π.left ⁻¹ᵁ U)]
  [IsScalarTower (Truncated.Witt.Ring p k n) Q Γ(X.left,π.left ⁻¹ᵁ U)]
  (τ : Fin g → Q)
  (hτ : ∀ j, algebraMap Q Γ(X.left,π.left ⁻¹ᵁ U) (τ j) = π.left.app U (t j))

include hτ in
omit [Fintype k] [CharP k p] in
theorem mapped_section :
    Integral.FormSectionUnit.unit (Truncated.Witt.Ring p k n) X g (π.left ⁻¹ᵁ U)
      (z • OrdinaryFormScalars.Ordinary.map (Truncated.Witt.Ring p k n) Q Γ(X.left,π.left ⁻¹ᵁ U) g
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol (Truncated.Witt.Ring p k n) Q 1 τ)) =
    selectedSection p k n X Z π U g t z := by
  rw [OrdinaryFormScalars.Ordinary.map_symbol, map_one]
  have ht : (fun j => algebraMap Q Γ(X.left,π.left ⁻¹ᵁ U) (τ j)) =
      Principal.DifferentialSymbolRestriction.sourceParameters
        (Truncated.Witt.Ring p k n) X Z π U t := funext hτ
  rw [ht]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SelectedFractionRestriction
