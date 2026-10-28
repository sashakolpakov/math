import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PointParameterData
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.PointParameterBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ConormalBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.EtaleCoordinateRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedDimension
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.Ideal
import Mathlib.RingTheory.Artinian.Ring

/-! # Parameter Existence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ParameterExistence.Chart

noncomputable section

/-! The regular point parameters, quotient bases and normal equations
needed by the residue comparison are supplied by the original smooth
projective geometry on an actual neighborhood of the entire section. -/
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

attribute [local instance] PointParameterData.Chart.ambientAlgebra

include hcontains hz in
theorem exists_parameters :
    ∃ (V : (Projective.IntrinsicOverlap.Intrinsic.space R N).Opens) (hV : IsAffineOpen V),
      V ≤ U ∧ Nonempty (PointParameterData.Chart.ParameterData X f z g V hV) := by
  let : Subsingleton (Spec (CommRingCat.of R)) := Ring.KrullDimLE.subsingleton_primeSpectrum R
  let p : Spec (CommRingCat.of R) := Classical.ofNonempty
  let : Nonempty X.left := ⟨z p⟩
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  let : SmoothOfRelativeDimension g (f.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) := by
    change SmoothOfRelativeDimension g (f.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R N).hom)
    rw [Over.w f]
    infer_instance
  have hg : g ≤ N := by
    simpa only [Fintype.card_fin, Nat.add_sub_cancel] using
      (IntegralComparison.Smooth.ClosedDimension.projective f.left g)
  let : SmoothOfRelativeDimension N (Projective.IntrinsicOverlap.Intrinsic.model R N).hom := by
    change SmoothOfRelativeDimension N (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (N+1)))
    simpa only [Fintype.card_fin, Nat.add_sub_cancel] using
      (Projective.RelativeDimension.smooth (R := R) (σ := Fin (N+1)))
  let : LocallyOfFiniteType (Projective.IntrinsicOverlap.Intrinsic.model R N).hom := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ_locallyOfFiniteType
  let : IsLocallyNoetherian (Projective.IntrinsicOverlap.Intrinsic.model R N).left :=
    LocallyOfFiniteType.isLocallyNoetherian (Projective.IntrinsicOverlap.Intrinsic.model R N).hom
  have hxU : f.left (z p) ∈ U := hcontains (show p ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
  have hcover : f.left (z p) ∈ ⨆ i : Fin (N+1), AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i := by
    rw [AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hcover
  obtain ⟨V₀, hV₀, hV₀U, hx₀, τ, hτ, a, hcoords, c, s, hs, hr, bI, hbI, hc, _⟩ :=
    IntegralComparison.Smooth.ClosedCoordinateNeighborhood.exists_neighborhood R X (Projective.IntrinsicOverlap.Intrinsic.model R N) f N g
      (U ⊓ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (z p) ⟨hxU,hxi⟩
  let := hτ
  let := a
  let := hcoords.1
  let := hcoords.2
  have hdim : c+g=N := by rw [hc, Nat.sub_add_cancel hg]
  have hcontains₀ : ⊤ ≤ z ⁻¹ᵁ (f.left ⁻¹ᵁ V₀) := by
    intro q _
    have hqp : q=p := Subsingleton.elim _ _
    change f.left (z q) ∈ V₀
    rw [hqp]
    exact hx₀
  obtain ⟨e,r,⟨D⟩⟩ := Intrinsic.PointParameterGeometry.exists_principal R X (Projective.IntrinsicOverlap.Intrinsic.model R N) f z hz
    V₀ hV₀ hcontains₀ τ s g (z p) hx₀ hs hr.toIsWeaklyRegular
  let V := (Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen r
  let hV : IsAffineOpen V := hV₀.basicOpen r
  have hVV₀ : V ≤ V₀ := (Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen_le r
  let s' := IdealSheafPrincipalEquations.sequence V₀ r s
  let hs' : Koszul.OrientedTopCohomology.ideal Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,V) s' = Projective.LocalAdjunction.ideal X f V hV :=
    IdealSheafPrincipalEquations.generates f.left.ker V₀ hV₀ r s hs
  have hp : KoszulPartial.Resolution.pointIdeal Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,V) s' D.parameter =
      (z ≫ f.left).ker.ideal ⟨V,hV⟩ := by
    rw [KoszulPoint.Ideal.append]
    exact Intrinsic.PointParameterGeometry.generates R X (Projective.IntrinsicOverlap.Intrinsic.model R N) f z hz V₀ hV₀ hcontains₀ τ s e r D
  let ρ : (f.left ⁻¹ᵁ V) ⟶ (f.left ⁻¹ᵁ V₀) := homOfLE (f.left.preimage_mono hVV₀)
  refine ⟨V,hV,hVV₀.trans (hV₀U.trans inf_le_left),⟨{
    coordinate := i
    below_coordinate := hVV₀.trans (hV₀U.trans inf_le_right)
    contains := D.contains
    codimension := c
    dimension := hdim
    equations := s'
    generates := hs'
    regular := IdealSheafPrincipalEquations.weaklyRegular V₀ hV₀ r s hr.toIsWeaklyRegular
    conormalBasis := Principal.ConormalBasis.basis f.left.ker V₀ hV₀ r bI
    conormalBasis_apply := Principal.ConormalBasis.basis_apply f.left.ker V₀ hV₀ r bI s hs hbI
    parameters := D.parameter
    quotientBasis := Intrinsic.PointParameterBasis.quotientBasis R X (Projective.IntrinsicOverlap.Intrinsic.model R N) f V₀ hV₀ τ e r
    quotientBasis_apply := Intrinsic.PointParameterBasis.quotientBasis_apply R X (Projective.IntrinsicOverlap.Intrinsic.model R N) f z hz
      V₀ hV₀ hcontains₀ τ e r s D
    point_generates := hp
    point_regular := D.regular
    coordinateIndex := τ
    finiteVariables := hτ
    coordinates := Affine.EtaleCoordinateRestriction.algebra R X ρ τ
    coordinateTower := Affine.EtaleCoordinateRestriction.tower R X ρ τ
    coordinateEtale := Affine.EtaleCoordinateRestriction.etale R X ρ τ
      (hV₀.preimage f.left) (hV.preimage f.left)
  }⟩⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ParameterExistence.Chart
