import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ParameterLiftRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.ParameterRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.SectionPrincipalNeighborhood

/-! # Paired Parameters -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PairedParameters.ParameterChart

noncomputable section

/-! A prescribed second parameter system on the closed scheme and an
original projective chart admit full frames on one ambient open.
Both parameter systems retain their literal restriction formulas. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

private theorem section_restriction_trans {X : Scheme.{u}} {U V W : X.Opens}
    (hVU : V ≤ U) (hWV : W ≤ V) (a : Γ(X,U)) :
    X.presheaf.map (homOfLE hWV).op (X.presheaf.map (homOfLE hVU).op a) =
      X.presheaf.map (homOfLE (hWV.trans hVU)).op a := by
  exact (ConcreteCategory.congr_hom
    (X.presheaf.map_comp (homOfLE hVU).op (homOfLE hWV).op) a).symm

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {N : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra PointParameterData.Chart.ambientAlgebra
variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R N)
  [IsClosedImmersion f.left] (z : Spec (CommRingCat.of R) ⟶ X.left)
  (g : ℕ) (U : (Projective.IntrinsicOverlap.Intrinsic.space R N).Opens) (hU : IsAffineOpen U)
  (D : PointParameterData.Chart.Data X f z g U hU) (W : X.left.Opens)
  (t : Fin g → Intrinsic.SmoothClosedSections.ring R X W)

structure PairedData where
  ambient : (Projective.IntrinsicOverlap.Intrinsic.space R N).Opens
  affine : IsAffineOpen ambient
  below : ambient ≤ U
  source_below : f.left ⁻¹ᵁ ambient ≤ W
  original : PointParameterData.Chart.Data X f z g ambient affine
  transported : PointParameterData.Chart.Data X f z g ambient affine
  same_codimension : transported.codimension = original.codimension
  same_coordinate : transported.coordinate = original.coordinate
  original_parameters : ∀ j, original.parameters j =
    (Projective.IntrinsicOverlap.Intrinsic.space R N).presheaf.map (homOfLE below).op (D.parameters j)
  transported_parameters : ∀ j, f.left.app ambient (transported.parameters j) =
    X.left.presheaf.map (homOfLE source_below).op (t j)

variable [IsArtinianRing R] [IsLocalRing R] [Smooth X.hom] [IsClosedImmersion z]
  (hz : z ≫ X.hom = 𝟙 _) (hW : IsAffineOpen W) (hcontains : ⊤ ≤ z ⁻¹ᵁ W)
  (ht : Ideal.span (Set.range t) = z.ker.ideal ⟨W,hW⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular
    (Intrinsic.SmoothClosedSections.ring R X W) (List.ofFn t))
  (b : Module.Basis (Fin g) (Intrinsic.SmoothClosedSections.ring R X W)
    Ω[Intrinsic.SmoothClosedSections.ring R X W⁄R])
  (hb : ∀ j, b j = KaehlerDifferential.D R _ (t j))

include hz hW hcontains ht hreg hb in
omit [IsNoetherianRing R] in
theorem exists_paired : Nonempty (PairedData X f z g U hU D W t) := by
  obtain ⟨r,hr,hrW⟩ := Closed.SectionPrincipalNeighborhood.exists_principal
    R X (Projective.IntrinsicOverlap.Intrinsic.model R N) f z hz U hU D.contains W hcontains
  let V := (Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen r
  let hV : IsAffineOpen V := hU.basicOpen r
  let D₁ := D.principal X f z g U hU r hr
  let t₁ := AffineOpen.ParameterRestriction.parameters R X W (f.left ⁻¹ᵁ V) hrW t
  have ht₁ : Ideal.span (Set.range t₁) = z.ker.ideal ⟨f.left ⁻¹ᵁ V,hV.preimage f.left⟩ :=
    AffineOpen.ParameterRestriction.span R X W (f.left ⁻¹ᵁ V) hW (hV.preimage f.left) hrW t z.ker ht
  have hreg₁ : RingTheory.Sequence.IsWeaklyRegular
      (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ V)) (List.ofFn t₁) :=
    AffineOpen.ParameterRestriction.regular R X W (f.left ⁻¹ᵁ V) hW (hV.preimage f.left) hrW t hreg
  let b₁ := AffineOpen.ParameterRestriction.basis R X W (f.left ⁻¹ᵁ V) hW (hV.preimage f.left) hrW b
  have hb₁ (j : Fin g) : b₁ j = KaehlerDifferential.D R _ (t₁ j) :=
    AffineOpen.ParameterRestriction.basis_apply R X W (f.left ⁻¹ᵁ V) hW (hV.preimage f.left) hrW t b hb j
  let P := D₁.toParameterData.replace X f z hz g V hV t₁ ht₁ hreg₁ b₁ hb₁
  let q := P.frameFunction X f z g V hV
  let hq : (Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen q ≤ V := (Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen_le q
  refine ⟨{
    ambient := (Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen q
    affine := hV.basicOpen q
    below := hq.trans ((Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen_le r)
    source_below := (f.left.preimage_mono hq).trans hrW
    original := D₁.restrictFor X f z g V hV P
    transported := P.framed X f z g V hV
    same_codimension := rfl
    same_coordinate := rfl
    original_parameters := ?_
    transported_parameters := ?_ }⟩
  · intro j
    exact section_restriction_trans ((Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen_le r) hq (D.parameters j)
  · intro j
    have hp := PointParameterData.Chart.ParameterData.replaced_framed_lift X f z g V hV hz D₁.toParameterData
      t₁ ht₁ hreg₁ b₁ hb₁ j
    exact hp.trans (section_restriction_trans hrW (f.left.preimage_mono hq) (t j))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PairedParameters.ParameterChart
