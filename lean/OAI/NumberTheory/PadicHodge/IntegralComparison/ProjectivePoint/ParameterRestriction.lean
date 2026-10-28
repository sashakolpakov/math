import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ParameterFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DifferentialBasis

/-! # Parameter Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ParameterRestriction.Chart

noncomputable section

/-! Literal principal restriction of projective point parameter data,
including its matching ambient differential basis. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

private theorem restricted_append {Y : Scheme.{u}} (U : Y.Opens) (r : Γ(Y,U))
    {c g : ℕ} (s : Fin c → Γ(Y,U)) (t : Fin g → Γ(Y,U)) :
    IdealSheafPrincipalEquations.sequence U r (Fin.append s t) =
      Fin.append (IdealSheafPrincipalEquations.sequence U r s)
        (IdealSheafPrincipalEquations.sequence U r t) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [IdealSheafPrincipalEquations.sequence, Fin.append_left, Fin.append_right]

private theorem reindex_reverse {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {r n : ℕ} (b : Module.Basis (Fin n) A M) (h : r=n) (i : Fin r) :
    (b.reindex (finCongr h.symm)) i = b (Fin.cast h i) := by
  subst n
  simp

private theorem reindex_forward {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {r n : ℕ} (b : Module.Basis (Fin r) A M) (h : r=n) (i : Fin r) :
    (b.reindex (finCongr h)) (Fin.cast h i) = b i := by
  subst n
  simp

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {N : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra PointParameterData.Chart.ambientAlgebra
variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R N)
  [IsClosedImmersion f.left] (z : Spec (CommRingCat.of R) ⟶ X.left)
  (g : ℕ) (U : (Projective.IntrinsicOverlap.Intrinsic.space R N).Opens) (hU : IsAffineOpen U)
  (r : Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,U))
  (hcontains : ⊤ ≤ z ⁻¹ᵁ (f.left ⁻¹ᵁ (Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen r))

def _root_.OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PointParameterData.Chart.ParameterData.principal (D : PointParameterData.Chart.ParameterData X f z g U hU) :
    PointParameterData.Chart.ParameterData X f z g ((Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen r) (hU.basicOpen r) := by
  let V := (Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen r
  let hV : IsAffineOpen V := hU.basicOpen r
  let s' := IdealSheafPrincipalEquations.sequence U r D.equations
  let t' := IdealSheafPrincipalEquations.sequence U r D.parameters
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
    rw [restricted_append] at hp
    exact hp
  have hr' : RingTheory.Sequence.IsWeaklyRegular Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,V) (List.ofFn (Fin.append s' t')) := by
    simpa only [restricted_append] using
      IdealSheafPrincipalEquations.weaklyRegular U hU r
        (Fin.append D.equations D.parameters) D.point_regular
  let ρ : (f.left ⁻¹ᵁ V) ⟶ (f.left ⁻¹ᵁ U) :=
    homOfLE (f.left.preimage_mono ((Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen_le r))
  let := D.finiteVariables
  let := D.coordinates
  let := D.coordinateTower
  let := D.coordinateEtale
  exact {
    coordinate := D.coordinate
    below_coordinate := ((Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen_le r).trans D.below_coordinate
    contains := hcontains
    codimension := D.codimension
    dimension := D.dimension
    equations := s'
    generates := IdealSheafPrincipalEquations.generates f.left.ker U hU r D.equations D.generates
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

omit [IsNoetherianRing R] in
theorem _root_.OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PointParameterData.Chart.ParameterData.principal_parameters (D : PointParameterData.Chart.ParameterData X f z g U hU) :
    (D.principal X f z g U hU r hcontains).parameters =
      IdealSheafPrincipalEquations.sequence U r D.parameters := rfl

def _root_.OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PointParameterData.Chart.Data.principal (D : PointParameterData.Chart.Data X f z g U hU) :
    PointParameterData.Chart.Data X f z g ((Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen r) (hU.basicOpen r) := by
  let V := (Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen r
  let hV : IsAffineOpen V := hU.basicOpen r
  let ρ : V ⟶ U := homOfLE ((Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen_le r)
  let b0 := D.ambientBasis.reindex (finCongr D.dimension.symm)
  have hb0 (i : Fin (D.codimension+g)) : b0 i =
      KaehlerDifferential.D R Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,U) (Fin.append D.equations D.parameters i) := by
    rw [reindex_reverse]
    have hi := congrFun D.ambientBasis_apply i
    refine hi.trans ?_
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [Fin.append_left, Fin.append_right]
  let bV := AffineOpen.DifferentialBasis.basis R (Projective.IntrinsicOverlap.Intrinsic.model R N) ρ hU hV b0
  refine {
    toParameterData := D.toParameterData.principal X f z g U hU r hcontains
    ambientBasis := bV.reindex (finCongr D.dimension)
    ambientBasis_apply := ?_ }
  funext i
  change Fin (D.codimension+g) at i
  change (bV.reindex (finCongr D.dimension)) (Fin.cast D.dimension i) =
    Fin.append
      (fun j => KaehlerDifferential.D R Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,V)
        (IdealSheafPrincipalEquations.sequence U r D.equations j))
      (fun j => KaehlerDifferential.D R Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,V)
        (IdealSheafPrincipalEquations.sequence U r D.parameters j)) i
  rw [reindex_forward]
  have hi := AffineOpen.DifferentialBasis.basis_apply R (Projective.IntrinsicOverlap.Intrinsic.model R N) ρ hU hV b0
    (Fin.append D.equations D.parameters) hb0 i
  refine hi.trans ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [Fin.append_left, Fin.append_right] <;> rfl

omit [IsNoetherianRing R] in
theorem _root_.OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PointParameterData.Chart.Data.principal_parameters (D : PointParameterData.Chart.Data X f z g U hU) :
    (D.principal X f z g U hU r hcontains).parameters =
      IdealSheafPrincipalEquations.sequence U r D.parameters := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ParameterRestriction.Chart
