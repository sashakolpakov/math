import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionPrincipalRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionGluing

/-! # Adjunction Global -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionGlobal

noncomputable section

/-! Global adjunction for the original projective negative resolution.
The map is assembled from the actual local purity, ambient-form and
conormal-residue isomorphisms, with their proved restriction laws. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionGluing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] LocalAdjunction.sectionIso

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ IntrinsicOverlap.Intrinsic.model R n)
  [IsClosedImmersion f.left] [Smooth X.hom] (g : ℕ)
  (j : Fin (n + 1)) (B : ℕ) (hB : n + 1 ≤ B) (hg : g ≤ n)

theorem data_restriction (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U)
    (D : AdjunctionCharts.Data X f g U hU) (i : Fin (n + 1)) (hi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    (r : Γ(IntrinsicOverlap.Intrinsic.space R n, U)) (s : Γ(AdjunctionGluing.sourceSheaf X f g j B, U)) :
    ((AdjunctionRestriction.data X f g D r).sectionIso X f g i
        (((IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r).trans hi) j B hB hg).hom
      ((AdjunctionGluing.sourceSheaf X f g j B).presheaf.map (homOfLE ((IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r)).op s) =
    (AdjunctionGluing.targetSheaf X f g).presheaf.map (homOfLE ((IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r)).op
      ((D.sectionIso X f g i hi j B hB hg).hom s) := by
  let D' := AdjunctionRestriction.data X f g D r
  let := D.finiteVariables
  let order : LinearOrder D.coordinateIndex :=
    LinearOrder.lift' (Fintype.equivFin D.coordinateIndex) (Fintype.equivFin D.coordinateIndex).injective
  exact @AdjunctionPrincipalRestriction.restriction R _ _ n X f _ _
    j B hB U hU i hi r (n - g) D.equations D.generates D.regular
    (ClosedImmersionPurity.targetTrivialization j (n + 1) U hU i hi)
    g (Nat.sub_add_cancel hg) D.conormalBasis D.quotientBasis
    D.coordinateIndex order D.coordinates D.coordinateTower D.coordinateEtale
    D'.coordinateIndex order D'.coordinates D'.coordinateTower D'.coordinateEtale s

variable [IsProper X.hom] [SmoothOfRelativeDimension g X.hom]

def iso : AdjunctionGluing.sourceSheaf X f g j B ≅ AdjunctionGluing.targetSheaf X f g :=
  AdjunctionGluing.iso X f g j B hB hg
    (data_restriction X f g j B hB hg)

theorem iso_app {U : (IntrinsicOverlap.Intrinsic.space R n).Opens} (hU : IsAffineOpen U) (h : AdjunctionCharts.Good X f g U)
    (s : Γ(AdjunctionGluing.sourceSheaf X f g j B, U)) :
    (iso X f g j B hB hg).hom.app U s =
      (ChartIndependence.AdjunctionCharts.chosenSectionIso X f g h j B hB hg).hom s :=
  AdjunctionGluing.iso_app X f g j B hB hg
    (data_restriction X f g j B hB hg) hU h s

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionGlobal
