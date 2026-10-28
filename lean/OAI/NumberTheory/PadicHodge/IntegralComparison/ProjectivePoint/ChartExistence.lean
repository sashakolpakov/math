import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ParameterExistence
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ParameterFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceBasisRestriction

/-! # Chart Existence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ChartExistence.Parameter

noncomputable section

/-! Full parameter charts for a smooth projective section, optionally
refined inside an actual finite étale trace chart. All chart data are
derived from the original geometric hypotheses. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsArtinianRing R] [IsLocalRing R]
  {N : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R N)
  [IsClosedImmersion f.left] (z : Spec (CommRingCat.of R) ⟶ X.left) [IsClosedImmersion z]
  (hz : z ≫ X.hom = 𝟙 _) (g : ℕ) [IsProper X.hom] [SmoothOfRelativeDimension g X.hom]
  (U : (Projective.IntrinsicOverlap.Intrinsic.space R N).Opens) (hcontains : ⊤ ≤ z ⁻¹ᵁ (f.left ⁻¹ᵁ U))

include hz hcontains in
theorem exists_chart :
    ∃ (V : (Projective.IntrinsicOverlap.Intrinsic.space R N).Opens) (hV : IsAffineOpen V),
      V ≤ U ∧ Nonempty (PointParameterData.Chart.Data X f z g V hV) := by
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  obtain ⟨V,hV,hVU,⟨D⟩⟩ := ParameterExistence.Chart.exists_parameters X f z hz g U hcontains
  obtain ⟨W,hW,hWV,_,⟨C⟩⟩ := PointParameterData.Chart.ParameterData.exists_frame X f z g V hV D
  exact ⟨W,hW,hWV.trans hVU,⟨C⟩⟩

variable (Y : Over (Spec (CommRingCat.of R))) (a : Y ⟶ X) [IsFinite a.left] [Etale a.left]

include hz hcontains in
theorem exists_finite_chart :
    ∃ (V : (Projective.IntrinsicOverlap.Intrinsic.space R N).Opens) (hV : IsAffineOpen V), V ≤ U ∧
      FiniteEtale.TraceBasis.Good R Y X a (f.left ⁻¹ᵁ V) ∧ Nonempty (PointParameterData.Chart.Data X f z g V hV) := by
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  let : Subsingleton (Spec (CommRingCat.of R)) := Ring.KrullDimLE.subsingleton_primeSpectrum R
  let p : Spec (CommRingCat.of R) := Classical.ofNonempty
  obtain ⟨W,hxW,_⟩ := FiniteEtale.TraceBasis.neighborhood R Y X a ⊤ (z p) trivial
  have hxU : f.left (z p) ∈ U := hcontains (show p ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
  obtain ⟨T,_,hxT,hTU,hTW⟩ := Closed.AffineNeighborhood.exists_subopen f.left U W.val (z p) hxU hxW
  have hcontainsT : ⊤ ≤ z ⁻¹ᵁ (f.left ⁻¹ᵁ T) := by
    intro q _
    have hqp : q=p := Subsingleton.elim _ _
    change f.left (z q) ∈ T
    rw [hqp]
    exact hxT
  obtain ⟨V,hV,hVT,⟨D⟩⟩ := exists_chart X f z hz g T hcontainsT
  have hVW : f.left ⁻¹ᵁ V ≤ W.val := (f.left.preimage_mono hVT).trans hTW
  exact ⟨V,hV,hVT.trans hTU,
    FiniteEtale.TraceBasisRestriction.good R Y X a W.val (f.left ⁻¹ᵁ V)
      W.property (hV.preimage f.left) hVW,⟨D⟩⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ChartExistence.Parameter
