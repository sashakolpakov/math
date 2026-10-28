import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PointParameterData
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ParameterFrameNeighborhood
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ConormalBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.QuotientBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.EtaleCoordinateRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SpaceSmooth
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.Ideal

/-! # Parameter Frame -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ParameterFrame.Chart

noncomputable section

/-! A genuine projective point parameter chart acquires its matching
ambient differential frame on a principal neighborhood, while its whole
closed chart and section are preserved. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

private theorem sequence_append {Y : Scheme.{u}} (U : Y.Opens) (r : Γ(Y,U))
    {c g : ℕ} (s : Fin c → Γ(Y,U)) (t : Fin g → Γ(Y,U)) :
    IdealSheafPrincipalEquations.sequence U r (Fin.append s t) =
      Fin.append (IdealSheafPrincipalEquations.sequence U r s)
        (IdealSheafPrincipalEquations.sequence U r t) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [IdealSheafPrincipalEquations.sequence, Fin.append_left, Fin.append_right]

private theorem reindex_cast {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {r n : ℕ} (b : Module.Basis (Fin r) A M) (h : r=n) (i : Fin r) :
    (b.reindex (finCongr h)) (Fin.cast h i) = b i := by
  subst n
  simp

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {N : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R N)
  [IsClosedImmersion f.left] (z : Spec (CommRingCat.of R) ⟶ X.left)
  (g : ℕ) (U : (Projective.IntrinsicOverlap.Intrinsic.space R N).Opens) (hU : IsAffineOpen U)

attribute [local instance] PointParameterData.Chart.ambientAlgebra

variable [Smooth X.hom]

omit [IsNoetherianRing R] in
theorem _root_.OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PointParameterData.Chart.ParameterData.exists_frame (D : PointParameterData.Chart.ParameterData X f z g U hU) :
    ∃ (V : (Projective.IntrinsicOverlap.Intrinsic.space R N).Opens) (hV : IsAffineOpen V),
      V ≤ U ∧ f.left ⁻¹ᵁ V = f.left ⁻¹ᵁ U ∧ Nonempty (PointParameterData.Chart.Data X f z g V hV) := by
  let : Smooth (Projective.IntrinsicOverlap.Intrinsic.model R N).hom := Projective.SpaceSmooth.smooth
  let sI := ConormalKoszulPurity.conormalVectors Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,U)
    (Projective.LocalAdjunction.ideal X f U hU) D.equations D.generates
  let b0 : Module.Basis (Fin (D.codimension+g)) Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,U) Ω[Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,U)⁄R] :=
    (Projective.AmbientAdjunction.differentialBasis D.coordinate U hU D.below_coordinate).reindex
      (finCongr D.dimension.symm)
  let r := Affine.ParameterFrameNeighborhood.determinant R X (Projective.IntrinsicOverlap.Intrinsic.model R N) f U hU
    sI D.parameters b0
  let V := (Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen r
  let hV : IsAffineOpen V := hU.basicOpen r
  have hVU : V ≤ U := (Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen_le r
  have hpre : f.left ⁻¹ᵁ V = f.left ⁻¹ᵁ U :=
    Affine.ParameterFrameNeighborhood.preimage R X (Projective.IntrinsicOverlap.Intrinsic.model R N) f U hU
      sI D.parameters b0 D.conormalBasis D.conormalBasis_apply D.quotientBasis D.quotientBasis_apply
  let s' := IdealSheafPrincipalEquations.sequence U r D.equations
  let t' := IdealSheafPrincipalEquations.sequence U r D.parameters
  let hs' : Koszul.OrientedTopCohomology.ideal Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,V) s' = Projective.LocalAdjunction.ideal X f V hV :=
    IdealSheafPrincipalEquations.generates f.left.ker U hU r D.equations D.generates
  have hp0 : Koszul.OrientedTopCohomology.ideal Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,U)
      (Fin.append D.equations D.parameters) = (z ≫ f.left).ker.ideal ⟨U,hU⟩ := by
    simpa only [KoszulPoint.Ideal.append] using D.point_generates
  have hp' : KoszulPartial.Resolution.pointIdeal Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,V) s' t' =
      (z ≫ f.left).ker.ideal ⟨V,hV⟩ := by
    rw [KoszulPoint.Ideal.append]
    have hp := IdealSheafPrincipalEquations.generates (z ≫ f.left).ker U hU r
      (Fin.append D.equations D.parameters) hp0
    change Koszul.OrientedTopCohomology.ideal Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,V)
      (IdealSheafPrincipalEquations.sequence U r (Fin.append D.equations D.parameters)) =
      (z ≫ f.left).ker.ideal ⟨V,hV⟩ at hp
    rw [sequence_append] at hp
    exact hp
  have hr' : RingTheory.Sequence.IsWeaklyRegular Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,V) (List.ofFn (Fin.append s' t')) := by
    simpa only [sequence_append] using
      IdealSheafPrincipalEquations.weaklyRegular U hU r
        (Fin.append D.equations D.parameters) D.point_regular
  let ρ : (f.left ⁻¹ᵁ V) ⟶ (f.left ⁻¹ᵁ U) := homOfLE (f.left.preimage_mono hVU)
  let := D.finiteVariables
  let := D.coordinates
  let := D.coordinateTower
  let := D.coordinateEtale
  let P : PointParameterData.Chart.ParameterData X f z g V hV :=
    { coordinate := D.coordinate
      below_coordinate := hVU.trans D.below_coordinate
      contains := by rw [hpre]; exact D.contains
      codimension := D.codimension
      dimension := D.dimension
      equations := s'
      generates := hs'
      regular := IdealSheafPrincipalEquations.weaklyRegular U hU r D.equations D.regular
      conormalBasis := Principal.ConormalBasis.basis f.left.ker U hU r D.conormalBasis
      conormalBasis_apply := Principal.ConormalBasis.basis_apply f.left.ker U hU r
        D.conormalBasis D.equations D.generates D.conormalBasis_apply
      parameters := t'
      quotientBasis := Principal.QuotientBasis.basis R (Projective.IntrinsicOverlap.Intrinsic.model R N) f.left.ker U hU r D.quotientBasis
      quotientBasis_apply := Principal.QuotientBasis.basis_apply R (Projective.IntrinsicOverlap.Intrinsic.model R N) f.left.ker U hU r
        D.quotientBasis D.parameters D.quotientBasis_apply
      point_generates := hp'
      point_regular := hr'
      coordinateIndex := D.coordinateIndex
      finiteVariables := D.finiteVariables
      coordinates := Affine.EtaleCoordinateRestriction.algebra R X ρ D.coordinateIndex
      coordinateTower := Affine.EtaleCoordinateRestriction.tower R X ρ D.coordinateIndex
      coordinateEtale := Affine.EtaleCoordinateRestriction.etale R X ρ D.coordinateIndex
        (hU.preimage f.left) (hV.preimage f.left) }
  let bV := Affine.ParameterFrameNeighborhood.basis R X (Projective.IntrinsicOverlap.Intrinsic.model R N) f U hU sI D.parameters b0
  have hbV := Affine.ParameterFrameNeighborhood.basis_eq R X (Projective.IntrinsicOverlap.Intrinsic.model R N) f U hU sI D.parameters b0
  refine ⟨V, hV, hVU, hpre, ⟨{
    toParameterData := P
    ambientBasis := bV.reindex (finCongr D.dimension)
    ambientBasis_apply := ?_
  }⟩⟩
  funext i
  exact (reindex_cast bV D.dimension i).trans (congrFun hbV i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ParameterFrame.Chart
