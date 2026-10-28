import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.ResidueRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.DifferentialSymbol

/-! # Differential Symbol Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.DifferentialSymbolRestriction

noncomputable section

/-! Restricting the actual differential-symbol section gives the
literal fraction on the reindexed principal diagram. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.SymbolCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R]
  (X Z : Over (Spec (CommRingCat.of R))) (π : X ⟶ Z)
  (U : Z.left.Opens) (hU : IsAffineOpen U)
  (V : X.left.Opens) (hV : IsAffineOpen V) (hVU : V ≤ π.left ⁻¹ᵁ U)
  {g : ℕ} (t : Fin g → Γ(Z.left,U))

local instance ambientAlgebra : Algebra R Γ(Z.left,U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R Z U
local instance sourceAlgebra (W : X.left.Opens) : Algebra R Γ(X.left,W) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X W

abbrev sourceParameters : Fin g → Γ(X.left,π.left ⁻¹ᵁ U) :=
  fun j => π.left.app U (t j)

abbrev parameters := PrincipalResidue.ResidueRestriction.parameters π.left U V hVU t

abbrev targetOpen := SectionPresheaf.openSubset V (PrincipalResidue.SymbolCoordinates.top V (parameters R X Z π U V hVU t))

def sourceValue (a : R) :=
  (DifferentialSymbol.map R X Z π U hU g (sourceParameters R X Z π U t)).app
    (op (PrincipalResidue.SymbolCoordinates.top U t)) (π.left.app (SectionPresheaf.openSubset U (PrincipalResidue.SymbolCoordinates.top U t)) (PrincipalResidue.SymbolCoordinates.coefficient U hU t R a))

theorem sourceValue_eq (a : R) : sourceValue R X Z π U hU t a =
    PrincipalResidue.SymbolCoordinates.symbolValue π.left U hU t R (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g)
      (DifferentialSymbol.generator R X Z π U g (sourceParameters R X Z π U t)) a := rfl

def targetValue (a : R) : Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g,
    targetOpen R X Z π U V hVU t) :=
  Integral.FormSectionUnit.unit R X g (targetOpen R X Z π U V hVU t)
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(X.left,targetOpen R X Z π U V hVU t)
      (PrincipalResidue.ResidueRestriction.coefficientMap π.left U V hV hVU t (PrincipalResidue.SymbolCoordinates.coefficient U hU t R a))
      (fun j => X.left.presheaf.map (SectionPresheaf.inclusion V (PrincipalResidue.SymbolCoordinates.top V (parameters R X Z π U V hVU t))).op
        (parameters R X Z π U V hVU t j)))

theorem restriction (a : R) :
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g).presheaf.map
      (homOfLE (PrincipalResidue.ResidueRestriction.topBelow π.left U V hV hVU t)).op
        (sourceValue R X Z π U hU t a) = targetValue R X Z π U hU V hV hVU t a := by
  rw [sourceValue, DifferentialSymbol.component,
    Integral.FormSectionUnit.restriction]
  erw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol]
  apply congrArg (Integral.FormSectionUnit.unit R X g (targetOpen R X Z π U V hVU t))
  congr 1
  funext j
  have hn := ConcreteCategory.congr_hom
    (π.left.naturality (SectionPresheaf.inclusion U (PrincipalResidue.SymbolCoordinates.top U t)).op) (t j)
  have h := congrArg
    (fun x => X.left.presheaf.map
      (homOfLE (PrincipalResidue.ResidueRestriction.topBelow π.left U V hV hVU t)).op x) hn.symm
  exact h.trans (PrincipalResidue.ResidueRestriction.map_restriction π.left U V hV hVU t (t j))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.DifferentialSymbolRestriction
