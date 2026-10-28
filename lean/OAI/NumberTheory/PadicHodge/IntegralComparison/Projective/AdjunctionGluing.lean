import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ComplementRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BasisGluingNormalization

/-! # Adjunction Gluing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionGluing

noncomputable section

/-! Principal compatibility on regular charts suffices to glue the
actual projective adjunction maps. The complement charts contribute
the unique maps between zero modules. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] AdjunctionCharts.Data.sectionIso ComplementAdjunction.sectionIso

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ IntrinsicOverlap.Intrinsic.model R n)
  [IsClosedImmersion f.left] [Smooth X.hom] (g : ℕ)
  (j : Fin (n + 1)) (B : ℕ) (hB : n + 1 ≤ B) (hg : g ≤ n)

abbrev sourceSheaf := (LocalAdjunction.dual X f j B).homology (n - g)
abbrev targetSheaf := Intrinsic.ClosedFormSections.directImage R X (IntrinsicOverlap.Intrinsic.model R n) f g

variable (hregular : ∀ (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U)
  (D : AdjunctionCharts.Data X f g U hU) (i : Fin (n + 1)) (hi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  (r : Γ(IntrinsicOverlap.Intrinsic.space R n, U)) (s : Γ(sourceSheaf X f g j B, U)),
  ((AdjunctionRestriction.data X f g D r).sectionIso X f g i
      (((IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r).trans hi) j B hB hg).hom
    ((sourceSheaf X f g j B).presheaf.map (homOfLE ((IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r)).op s) =
  (targetSheaf X f g).presheaf.map (homOfLE ((IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r)).op
    ((D.sectionIso X f g i hi j B hB hg).hom s))

include hregular in
theorem chart_principal {U : (IntrinsicOverlap.Intrinsic.space R n).Opens} (C : AdjunctionCharts.Chart X f g U)
    (r : Γ(IntrinsicOverlap.Intrinsic.space R n, U)) (s : Γ(sourceSheaf X f g j B, U)) :
    ((AdjunctionRestriction.chart X f g C r).sectionIso X f g j B hB hg).hom
        ((sourceSheaf X f g j B).presheaf.map (homOfLE ((IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r)).op s) =
      (targetSheaf X f g).presheaf.map (homOfLE ((IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r)).op
        ((C.sectionIso X f g j B hB hg).hom s) := by
  cases C with
  | mk hU i hi d =>
    cases d with
    | inl h =>
      exact AdjunctionCharts.Chart.complement_restriction X f g ⟨hU, i, hi, Sum.inl h⟩
        (AdjunctionRestriction.chart X f g ⟨hU, i, hi, Sum.inl h⟩ r)
        h.down ((IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r) j B hB hg s
    | inr D => exact hregular U hU D i hi r s

include hregular in
theorem chosen_principal {U : (IntrinsicOverlap.Intrinsic.space R n).Opens} (h : AdjunctionCharts.Good X f g U)
    (r : Γ(IntrinsicOverlap.Intrinsic.space R n, U)) (s : Γ(sourceSheaf X f g j B, U)) :
    (ChartIndependence.AdjunctionCharts.chosenSectionIso X f g (AdjunctionRestriction.good_principal X f g h r)
        j B hB hg).hom
      ((sourceSheaf X f g j B).presheaf.map (homOfLE ((IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r)).op s) =
    (targetSheaf X f g).presheaf.map (homOfLE ((IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r)).op
      ((ChartIndependence.AdjunctionCharts.chosenSectionIso X f g h j B hB hg).hom s) := by
  let C := Classical.choice h
  rw [ChartIndependence.AdjunctionCharts.chosenSectionIso_eq X f g _ (AdjunctionRestriction.chart X f g C r),
    ChartIndependence.AdjunctionCharts.chosenSectionIso_eq X f g h C]
  exact chart_principal X f g j B hB hg hregular C r s

variable [IsProper X.hom] [SmoothOfRelativeDimension g X.hom]

def iso : sourceSheaf X f g j B ≅ targetSheaf X f g :=
  Principal.BasisGluing.iso (sourceSheaf X f g j B) (targetSheaf X f g) (AdjunctionCharts.Good X f g)
    (fun _ _ h => (ChartIndependence.AdjunctionCharts.chosenSectionIso X f g h j B hB hg).hom.hom)
    (fun _ _ h r => AdjunctionRestriction.good_principal X f g h r)
    (fun _ _ h r s => chosen_principal X f g j B hB hg hregular h r s)
    (AdjunctionCharts.exists_neighborhood X f g)
    (fun _ _ h => ConcreteCategory.bijective_of_isIso (ChartIndependence.AdjunctionCharts.chosenSectionIso X f g h j B hB hg).hom)

theorem iso_app {U : (IntrinsicOverlap.Intrinsic.space R n).Opens} (hU : IsAffineOpen U) (h : AdjunctionCharts.Good X f g U)
    (s : Γ(sourceSheaf X f g j B, U)) :
    (iso X f g j B hB hg hregular).hom.app U s =
      (ChartIndependence.AdjunctionCharts.chosenSectionIso X f g h j B hB hg).hom s :=
  Principal.BasisGluingNormalization.iso_app (sourceSheaf X f g j B) (targetSheaf X f g) (AdjunctionCharts.Good X f g)
    (fun _ _ h => (ChartIndependence.AdjunctionCharts.chosenSectionIso X f g h j B hB hg).hom.hom)
    (fun _ _ h r => AdjunctionRestriction.good_principal X f g h r)
    (fun _ _ h r s => chosen_principal X f g j B hB hg hregular h r s)
    (AdjunctionCharts.exists_neighborhood X f g)
    (fun _ _ h => ConcreteCategory.bijective_of_isIso (ChartIndependence.AdjunctionCharts.chosenSectionIso X f g h j B hB hg).hom)
    U hU h s

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionGluing
