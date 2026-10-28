import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueDimensionData

/-! # Coefficient Residue Concentration -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueConcentration

noncomputable section

/-! The actual finite coefficient residue first passes through the
original sheaf concentration and the genuine survivor map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.Module Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomLocal OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {c g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
  Projective.LocalAdjunction.ambientAlgebra Projective.ParameterChart.coordinateOrder
attribute [local instance] Finite.FlatCoefficientSections.quotientAlgebra
  Finite.FlatCoefficientSections.coefficientAlgebra Finite.FlatCoefficientSections.ambientAlgebra
attribute [local instance] ProjectiveCoefficient.HomLocal.coefficient_terms
variable (X : Over (Spec (CommRingCat.of R))) {Y : Scheme.{u}}
  (f : Y ⟶ X.left) [IsFinite f] [Flat f]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (c+g)) [IsClosedImmersion i.left]
  [Smooth X.hom] [IsProper X.hom] [SmoothOfRelativeDimension g X.hom]
  (j : Fin (c+g+1)) (B : ℕ) (hB : c+g+1≤B)
  (U : (Projective.IntrinsicOverlap.Intrinsic.space R (c+g)).Opens) (hU : IsAffineOpen U)
  (k : Fin (c+g+1)) (hUk : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)
  (s : Fin c → Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g),U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g),U) s = Projective.LocalAdjunction.ideal X i U hU)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g),U) (List.ofFn s))
  (b : Basis (Fin (c+g)) Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g),U) Ω[Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g),U)⁄R])
  (P : ProjectiveResolution (ModuleCat.of Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g),U) (Finite.FlatCoefficientSections.coefficientRing f i.left U)))
  {ι : Type u} [LinearOrder ι] (W : ι → Principal.SectionPresheaf.Index U) (q : ℕ)

abbrev concentrationWith (x : Finite.FlatCoefficientSections.coefficientRing f i.left U) := by
  let : (ProjectiveCoefficient.HomLocal.coefficient X f i).IsQuasicoherent := Finite.MapPureTrace.coefficients_quasicoherent f i.left
  let : (ProjectiveCoefficient.HomLocal.coefficient X f i).IsFiniteType := Finite.MapPureTrace.coefficients_finiteType f i.left
  let : (ProjectiveCoefficient.HomLocal.canonical (R := R) j).IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible j (c+g+1))
  let (r : ℕ) := ProjectiveCoefficient.HomLocal.coefficient_dual_terms X f i j B hB r
  let (r : ℕ) := ProjectiveCoefficient.HomLocal.coefficient_term_projective X f i j B U hU k hUk r
  let : Algebra
      (Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g),U) ⧸ KoszulPartial.Resolution.normalIdeal Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g),U) s)
      (Finite.FlatCoefficientSections.coefficientRing f i.left U) :=
    FiniteCoefficient.QuotientAction.algebra f i.left U hU s hs
  let : IsScalarTower Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g),U)
      (Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g),U) ⧸ KoszulPartial.Resolution.normalIdeal Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g),U) s)
      (Finite.FlatCoefficientSections.coefficientRing f i.left U) :=
    FiniteCoefficient.QuotientAction.tower f i.left U hU s hs
  exact Principal.CoefficientResidueConcentration.concentration U hU (ProjectiveCoefficient.HomLocal.canonical j)
    (Projective.PrincipalResidueCoordinates.scalarFrame (c := c+g) (g := 0) j U hU k hUk b)
    (ProjectiveCoefficient.HomLocal.coefficient X f i) (ProjectiveCoefficient.HomLocal.coefficientComplex X f i j B)
    (Projective.NegativeResolution.augmentation (ProjectiveCoefficient.HomLocal.coefficient X f i) j B)
    (ModuleCat.of Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g),U) (Finite.FlatCoefficientSections.coefficientRing f i.left U))
    (Finite.FlatCoefficientSections.chartIso f i.left U hU) P i.left s hs hreg
    (Koszul.CoefficientPointFraction.vector Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g),U) s (Finite.FlatCoefficientSections.coefficientRing f i.left U) x)
    W (CoefficientResidueDimensionData.exactAt rfl X f i j B hB) q

abbrev concentration (x : Finite.FlatCoefficientSections.coefficientRing f i.left U) :=
  concentrationWith X f i j B hB U hU k hUk s hs hreg b
    (CoefficientResidueAdjunctionData.resolution X f i j B U hU k hUk) W q x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueConcentration
