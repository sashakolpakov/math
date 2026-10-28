import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionCharts
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionIndependence

/-! # Chart Independence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective

noncomputable section

/-! The local adjunction map is canonical on each good affine open,
including opens where both sheaves vanish. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ IntrinsicOverlap.Intrinsic.model R n)
  [IsClosedImmersion f.left] [Smooth X.hom] (g : ℕ)
  {U : (IntrinsicOverlap.Intrinsic.space R n).Opens} {hU : IsAffineOpen U}

theorem AdjunctionCharts.Data.sectionIso_eq (D E : AdjunctionCharts.Data X f g U hU)
    (i k : Fin (n + 1)) (hi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (hk : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)
    (j : Fin (n + 1)) (B : ℕ) (hB : n + 1 ≤ B) (hg : g ≤ n) :
    D.sectionIso X f g i hi j B hB hg = E.sectionIso X f g k hk j B hB hg := by
  let := D.finiteVariables
  let := E.finiteVariables
  let : LinearOrder D.coordinateIndex :=
    LinearOrder.lift' (Fintype.equivFin D.coordinateIndex) (Fintype.equivFin D.coordinateIndex).injective
  let : LinearOrder E.coordinateIndex :=
    LinearOrder.lift' (Fintype.equivFin E.coordinateIndex) (Fintype.equivFin E.coordinateIndex).injective
  let := D.coordinates
  let := E.coordinates
  let := D.coordinateTower
  let := E.coordinateTower
  let := D.coordinateEtale
  let := E.coordinateEtale
  exact AdjunctionIndependence.same_open X f j B hB U hU i k hi hk
    (Nat.sub_add_cancel hg) D.equations D.generates D.regular D.conormalBasis D.conormalBasis_apply
    E.equations E.generates E.regular E.conormalBasis E.conormalBasis_apply
    D.quotientBasis E.quotientBasis D.coordinateIndex E.coordinateIndex

theorem AdjunctionCharts.Chart.sectionIso_eq (C D : AdjunctionCharts.Chart X f g U)
    (j : Fin (n + 1)) (B : ℕ) (hB : n + 1 ≤ B) (hg : g ≤ n) :
    C.sectionIso X f g j B hB hg = D.sectionIso X f g j B hB hg := by
  cases C with
  | mk hC i hi c =>
    cases D with
    | mk hD k hk d =>
      cases c with
      | inl hc =>
        apply Iso.ext
        exact (ComplementAdjunction.dual_sections_zero f.left j B (n + 1) hB
          U hC i hi hc.down (n - g)).eq_of_src _ _
      | inr C =>
        cases d with
        | inl hd =>
          apply Iso.ext
          exact (ComplementAdjunction.dual_sections_zero f.left j B (n + 1) hB
            U hD k hk hd.down (n - g)).eq_of_src _ _
        | inr D =>
          exact C.sectionIso_eq X f g D i k hi hk j B hB hg

def ChartIndependence.AdjunctionCharts.chosenSectionIso (h : AdjunctionCharts.Good X f g U)
    (j : Fin (n + 1)) (B : ℕ) (hB : n + 1 ≤ B) (hg : g ≤ n) :
    (Affine.ModuleExactSections.sections U).obj ((LocalAdjunction.dual X f j B).homology (n - g)) ≅
      (Affine.ModuleExactSections.sections U).obj
        (Intrinsic.ClosedFormSections.directImage R X (IntrinsicOverlap.Intrinsic.model R n) f g) :=
  (Classical.choice h).sectionIso X f g j B hB hg

theorem ChartIndependence.AdjunctionCharts.chosenSectionIso_eq (h : AdjunctionCharts.Good X f g U) (C : AdjunctionCharts.Chart X f g U)
    (j : Fin (n + 1)) (B : ℕ) (hB : n + 1 ≤ B) (hg : g ≤ n) :
    ChartIndependence.AdjunctionCharts.chosenSectionIso X f g h j B hB hg = C.sectionIso X f g j B hB hg :=
  AdjunctionCharts.Chart.sectionIso_eq X f g (Classical.choice h) C j B hB hg

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective
