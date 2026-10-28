import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueAdjunctionData

/-! # Coefficient Residue Adjunction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueAdjunction

noncomputable section

/-! On a genuine projective parameter chart, every finite coefficient
section evaluates the original adjunction by the original coefficient residue. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial _root_.Module
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomLocal OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {c g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
  Projective.ParameterNeighborhood.sectionAlgebra Projective.ParameterChart.coordinateOrder
attribute [local instance] Finite.FlatCoefficientSections.quotientAlgebra
  Finite.FlatCoefficientSections.coefficientAlgebra
  Finite.FlatCoefficientSections.ambientAlgebra
attribute [local instance] ProjectiveCoefficient.HomLocal.scalar_terms
  ProjectiveCoefficient.HomLocal.coefficient_terms
variable (X : Over (Spec (CommRingCat.of R))) {Y : Scheme.{u}}
  (f : Y ⟶ X.left) [IsFinite f] [Flat f]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (c+g)) [IsClosedImmersion i.left]
  [Smooth X.hom] [IsProper X.hom] [SmoothOfRelativeDimension g X.hom]
  (j : Fin (c+g+1)) (B : ℕ) (hB : c+g+1≤B)
  (U : (Projective.IntrinsicOverlap.Intrinsic.space R (c+g)).Opens) (hU : IsAffineOpen U)
  (k : Fin (c+g+1)) (hUk : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)
  (s : Fin c → Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U) s = Projective.LocalAdjunction.ideal X i U hU)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U) (List.ofFn s))
  (bI : Basis (Fin c) (Projective.LocalAdjunction.quotient X i U hU) (Projective.LocalAdjunction.ideal X i U hU).Cotangent)
  (hI : ∀ a, bI a = (Projective.LocalAdjunction.ideal X i U hU).toCotangent
    (ConormalKoszulPurity.conormalVectors Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U) (Projective.LocalAdjunction.ideal X i U hU) s hs a))
  (bQ : Basis (Fin g) (Projective.LocalAdjunction.quotient X i U hU) Ω[Projective.LocalAdjunction.quotient X i U hU⁄R])
  (t : Fin g → Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U))
  (ht : ∀ a, bQ a = KaehlerDifferential.D R (Projective.LocalAdjunction.quotient X i U hU)
    (Ideal.Quotient.mk (Projective.LocalAdjunction.ideal X i U hU) (t a)))
  (b : Basis (Fin (c+g)) Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U) Ω[Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U)⁄R])
  (hb : (b : Fin (c+g) → Ω[Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U)⁄R]) =
    Fin.append (fun a => KaehlerDifferential.D R Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U) (s a))
      (fun a => KaehlerDifferential.D R Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U) (t a)))
  (τ : Type u) [Fintype τ]
  [Algebra (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (i.left ⁻¹ᵁ U))]
  [IsScalarTower R (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (i.left ⁻¹ᵁ U))]
  [Algebra.Etale (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (i.left ⁻¹ᵁ U))]

open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueAdjunctionData

abbrev rawComparisonWith
    (P : ProjectiveResolution (ModuleCat.of Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U) (Finite.FlatCoefficientSections.coefficientRing f i.left U)))
    (x : Finite.FlatCoefficientSections.coefficientRing f i.left U) := by
  let : (ProjectiveCoefficient.HomLocal.coefficient X f i).IsQuasicoherent := Finite.MapPureTrace.coefficients_quasicoherent f i.left
  let : (ProjectiveCoefficient.HomLocal.coefficient X f i).IsFiniteType := Finite.MapPureTrace.coefficients_finiteType f i.left
  let : (ProjectiveCoefficient.HomLocal.canonical (R := R) j).IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible j (c+g+1))
  let (q : ℕ) : ((ProjectiveCoefficient.HomLocal.scalarComplex X i j B).X q).IsQuasicoherent :=
    ProjectiveCoefficient.HomLocal.scalar_terms X i j B q
  let (q : ℕ) : ((ProjectiveCoefficient.HomLocal.coefficientComplex X f i j B).X q).IsQuasicoherent :=
    ProjectiveCoefficient.HomLocal.coefficient_terms X f i j B q
  let (q : ℕ) := ProjectiveCoefficient.HomLocal.scalar_dual_terms X i j B hB q
  let (q : ℕ) := ProjectiveCoefficient.HomLocal.coefficient_dual_terms X f i j B hB q
  let (q : ℕ) := ProjectiveCoefficient.HomLocal.scalar_projective X i j B U hU k hUk q
  let (q : ℕ) := ProjectiveCoefficient.HomLocal.coefficient_term_projective X f i j B U hU k hUk q
  let := IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent R X g
  let ε := Projective.NegativeResolution.augmentation (ProjectiveCoefficient.HomLocal.scalar X i) j B
  let ε' := Projective.NegativeResolution.augmentation (ProjectiveCoefficient.HomLocal.coefficient X f i) j B
  let : QuasiIso ε :=
    inferInstanceAs (QuasiIso (Projective.NegativeResolution.augmentation (ProjectiveCoefficient.HomLocal.scalar X i) j B))
  let : QuasiIso ε' :=
    inferInstanceAs (QuasiIso (Projective.NegativeResolution.augmentation (ProjectiveCoefficient.HomLocal.coefficient X f i) j B))
  exact FiniteCoefficient.ResidueAdjunction.comparison f i.left U hU
    (ProjectiveCoefficient.HomLocal.scalarComplex X i j B) (ProjectiveCoefficient.HomLocal.coefficientComplex X f i j B) ε ε' (ProjectiveCoefficient.HomLocal.canonical j)
    (Projective.PrincipalResidueCoordinates.scalarFrame j U hU k hUk b) s hs hreg P
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g)
    (Principal.DifferentialSymbol.generator R X (Projective.IntrinsicOverlap.Intrinsic.model R (c+g)) i U g
      (fun a => i.left.app U (t a)))
    (Projective.ParameterGlobalCoordinates.iso X i (Nat.add_sub_cancel c g).symm
      j B hB (Nat.le_add_left g c)).hom
    (ProjectiveCoefficient.HomDegreeCoordinates.iso X f i g c
      (Nat.add_sub_cancel c g).symm j B hB (Nat.le_add_left g c)).hom x
    (Projective.ResidueLocalAdjunction.comparison X i j B hB U hU k hUk
      s hs hreg bI hI bQ t ht b hb τ)
    (fun z => CoefficientEvaluation.evaluation X f i g c
      (Nat.add_sub_cancel c g).symm j B hB (Nat.le_add_left g c) U hU k hUk z x)

include hI ht hb τ in
theorem comparisonWith
    (P : ProjectiveResolution (ModuleCat.of Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U) (Finite.FlatCoefficientSections.coefficientRing f i.left U)))
    (x : Finite.FlatCoefficientSections.coefficientRing f i.left U) :
    CoefficientResidueAdjunctionData.homMap X f i j B hB U hU ≫ CoefficientResidueAdjunctionData.evaluation X f i U hU x =
      CoefficientResidueAdjunctionData.survivor X f i j B hB U hU k hUk s hs hreg b P x ≫ CoefficientResidueAdjunctionData.symbol X i U hU t :=
  rawComparisonWith X f i j B hB U hU k hUk s hs hreg bI hI bQ t ht b hb τ P x

abbrev comparison (x : Finite.FlatCoefficientSections.coefficientRing f i.left U) :=
  comparisonWith X f i j B hB U hU k hUk s hs hreg bI hI bQ t ht b hb τ
    (CoefficientResidueAdjunctionData.resolution X f i j B U hU k hUk) x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueAdjunction
