import OAI.AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Diagram -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram

noncomputable section

/-! Principal localizations of an affine open give their actual affine
subopens in the ambient scheme, with the original restriction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u
variable (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)

def object (r : OAI.AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Γ(X, U)) : X.affineOpens :=
  ⟨X.basicOpen r.val, hU.basicOpen r.val⟩

theorem monotone : Monotone (object X U hU) := by
  intro r s hrs
  change X.basicOpen r.val ≤ X.basicOpen s.val
  rw [← hU.fromSpec_image_basicOpen, ← hU.fromSpec_image_basicOpen]
  exact hU.fromSpec.image_mono hrs

def functor : OAI.AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Γ(X, U) ⥤ X.affineOpens :=
  (monotone X U hU).functor

def projection (r : OAI.AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Γ(X, U)) :
    (Diagram.functor X U hU).obj r ⟶ ⟨U, hU⟩ :=
  homOfLE (X.basicOpen_le r.val)

theorem projection_natural {r s : OAI.AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Γ(X, U)} (a : r ⟶ s) :
    (Diagram.functor X U hU).map a ≫ projection X U hU s = projection X U hU r :=
  Subsingleton.elim _ _

include hU in
theorem restricted_function_isUnit (r : OAI.AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Γ(X, U)) :
    IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le r.val)).op).hom r.val) := by
  let : IsLocalization.Away r.val Γ(X, X.basicOpen r.val) :=
    IsAffineOpen.isLocalization_basicOpen hU r.val
  exact IsLocalization.Away.algebraMap_isUnit r.val

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram
