import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ChartIndependence

/-! # Complement Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective

noncomputable section

/-! On an affine open disjoint from the closed subscheme, the native
adjunction maps commute with every further restriction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ IntrinsicOverlap.Intrinsic.model R n)
  [IsClosedImmersion f.left] [Smooth X.hom] (g : ℕ)
  {U V : (IntrinsicOverlap.Intrinsic.space R n).Opens}

theorem AdjunctionCharts.Chart.complement_restriction (C : AdjunctionCharts.Chart X f g U) (D : AdjunctionCharts.Chart X f g V)
    (hunit : RingHom.ker (f.left.app U).hom = ⊤) (hVU : V ≤ U)
    (j : Fin (n + 1)) (B : ℕ) (hB : n + 1 ≤ B) (hg : g ≤ n)
    (s : Γ((LocalAdjunction.dual X f j B).homology (n - g), U)) :
    (D.sectionIso X f g j B hB hg).hom
        (((LocalAdjunction.dual X f j B).homology (n - g)).presheaf.map (homOfLE hVU).op s) =
      (Intrinsic.ClosedFormSections.directImage R X (IntrinsicOverlap.Intrinsic.model R n) f g).presheaf.map
        (homOfLE hVU).op ((C.sectionIso X f g j B hB hg).hom s) := by
  let : Subsingleton Γ((LocalAdjunction.dual X f j B).homology (n - g), U) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (ComplementAdjunction.dual_sections_zero f.left j B (n + 1) hB
        U C.affine C.coordinate C.le_coordinate hunit (n - g))
  have hs : s = 0 := Subsingleton.elim _ _
  rw [hs]
  simp only [map_zero]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective
