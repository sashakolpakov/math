import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleAdjunctionPairing
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientWeight
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.CoefficientLocalClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SectionUnit

/-! # Etale Point Pairing Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.EtalePointPairingData

noncomputable section

/-! Every coefficient pairing of the actual finite local point class
is section evaluation times the same original scalar point residue.
The affine basis data are the genuine projective parameter chart. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.Module Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
private theorem reweight {A M : Type*} [SMul A M]
    (x y : M) (a b : A) (h : x = a • y) (hab : a = b) : x = b • y := by
  rw [← hab]
  exact h

private theorem map_weight {A : Type u} [CommRing A] {M N : ModuleCat.{u} A}
    (f : M ⟶ N) (x y : M) (a : A) (h : x = a • y) : f x = a • f y := by
  rw [h, map_smul]

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomLocal OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  [IsArtinianRing R] [IsLocalRing R] {n c g : ℕ} (hcg : c+g=n+1)
attribute [local instance] MvPolynomial.gradedAlgebra
  Projective.LocalAdjunction.ambientAlgebra Projective.ParameterChart.coordinateOrder
attribute [local instance] Finite.FlatCoefficientSections.quotientAlgebra
  Finite.FlatCoefficientSections.coefficientAlgebra Finite.FlatCoefficientSections.ambientAlgebra
variable (X Y : Over (Spec (CommRingCat.of R))) [Nonempty X.left] (f : Y ⟶ X)
  [IsFinite f.left] [Etale f.left]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) [IsClosedImmersion i.left]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom]
  [SmoothOfRelativeDimension g X.hom]
  (s₀ : Spec (CommRingCat.of R) ⟶ Y.left) (hbase : s₀ ≫ Y.hom = 𝟙 _)
  (B : ℕ) (hB : n+2≤B)
  (U : (Projective.IntrinsicOverlap.Intrinsic.space R (n+1)).Opens) (hU : IsAffineOpen U)
  (hcontains : ⊤ ≤ ((s₀ ≫ f.left) ≫ i.left) ⁻¹ᵁ U)
  (k : Fin (n+2)) (hUk : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)
  (s : Fin c → Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U) s = Projective.LocalAdjunction.ideal X i U hU)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U) (List.ofFn s))
  (bI : Basis (Fin c) (Projective.LocalAdjunction.quotient X i U hU) (Projective.LocalAdjunction.ideal X i U hU).Cotangent)
  (hI : ∀ a, bI a = (Projective.LocalAdjunction.ideal X i U hU).toCotangent
    (ConormalKoszulPurity.conormalVectors Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U) (Projective.LocalAdjunction.ideal X i U hU) s hs a))
  (bQ : Basis (Fin g) (Projective.LocalAdjunction.quotient X i U hU) Ω[Projective.LocalAdjunction.quotient X i U hU⁄R])
  (t : Fin g → Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U))
  (ht : ∀ a, bQ a = KaehlerDifferential.D R (Projective.LocalAdjunction.quotient X i U hU)
    (Ideal.Quotient.mk (Projective.LocalAdjunction.ideal X i U hU) (t a)))
  (hst : KoszulPartial.Resolution.pointIdeal Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U) s t =
    ((s₀ ≫ f.left) ≫ i.left).ker.ideal ⟨U,hU⟩)
  (hregst : RingTheory.Sequence.IsWeaklyRegular Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U) (List.ofFn (Fin.append s t)))
  (b : Basis (Fin (n+1)) Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U) Ω[Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U)⁄R])
  (hb : (fun a : Fin (c+g) => b (Fin.cast hcg a)) =
    Fin.append (fun a => KaehlerDifferential.D R Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U) (s a))
      (fun a => KaehlerDifferential.D R Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U) (t a)))
  (τ : Type u) [Fintype τ]
  [Algebra (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (i.left ⁻¹ᵁ U))]
  [IsScalarTower R (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (i.left ⁻¹ᵁ U))]
  [Algebra.Etale (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (i.left ⁻¹ᵁ U))]

local instance composite_smooth : Smooth (i.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) := by
  change Smooth (i.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)).hom)
  rw [Over.w i]
  infer_instance
local instance composite_proper : IsProper (i.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) := by
  change IsProper (i.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)).hom)
  rw [Over.w i]
  infer_instance
local instance composite_connected : GeometricallyConnected (i.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) := by
  change GeometricallyConnected (i.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)).hom)
  rw [Over.w i]
  infer_instance

abbrev pairingPoint (x : Finite.FlatCoefficientSections.coefficientRing f.left i.left U) := by
  letI : Subsingleton (Spec (CommRingCat.of R)) := Ring.KrullDimLE.subsingleton_primeSpectrum R
  let hsec := FiniteEtale.SectionUnit.section_over X Y f i s₀ hbase
  letI : IsClosedImmersion (s₀ ≫ f.left) :=
    isClosedImmersion_of_comp_eq_id (i.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (s₀ ≫ f.left) hsec
  letI := Finite.MapPureTrace.coefficients_quasicoherent f.left i.left
  letI := Finite.MapPureTrace.coefficients_finiteType f.left i.left
  let j := ProjectivePoint.Survivor.chart (R := R) (n := n)
  let W := PrincipalPoint.Fraction.family U t
  let y := ProjectivePoint.CoefficientLocalClass.value i.left (s₀ ≫ f.left) hsec B hB
    (Cech.StructurePullbackUnit.coefficients f.left i.left)
    (Cech.SectionCoefficientUnit.sheafMap s₀ f.left i.left) U hU s t hst hcg
  have hp := Principal.FiniteEtaleAdjunctionPairing.comparison hcg X Y f i j B hB U hU W (c+g)
    k hUk s hs hreg bI hI bQ t ht b hb τ x
  exact ConcreteCategory.congr_hom hp y

abbrev scalarImage (x : Finite.FlatCoefficientSections.coefficientRing f.left i.left U) := by
  letI : Subsingleton (Spec (CommRingCat.of R)) := Ring.KrullDimLE.subsingleton_primeSpectrum R
  let hsec := FiniteEtale.SectionUnit.section_over X Y f i s₀ hbase
  letI : IsClosedImmersion (s₀ ≫ f.left) :=
    isClosedImmersion_of_comp_eq_id (i.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (s₀ ≫ f.left) hsec
  let H := Supported.CechHomotopyEquivalence.functor (R := Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U))
    (PrincipalPoint.Fraction.family U t) (c+g)
  let S := single ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤
    ModuleCat.{u} Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U)) (.up ℕ) c
  let e := Projective.PrincipalResidueCoordinates.scalarFrame (c := n+1) (g := 0)
    (ProjectivePoint.Survivor.chart (R := R) (n := n)) U hU k hUk b
  let mul := Principal.DifferentialSymbol.map R X (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) i U hU g
    (fun a => i.left.app U (t a))
  have hr := CoefficientResidueClass.fixedPoint_scalar f.left i.left s₀ hsec
    B hB U hU hcontains k hUk e s t hs hst hreg hregst hcg x
  exact map_weight (H.map (S.map mul)) _ _ _ hr

abbrev weightedResidue (x : Finite.FlatCoefficientSections.coefficientRing f.left i.left U) := by
  letI : Subsingleton (Spec (CommRingCat.of R)) := Ring.KrullDimLE.subsingleton_primeSpectrum R
  let hsec := FiniteEtale.SectionUnit.section_over X Y f i s₀ hbase
  letI : IsClosedImmersion (s₀ ≫ f.left) :=
    isClosedImmersion_of_comp_eq_id (i.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (s₀ ≫ f.left) hsec
  have hr := scalarImage (hcg := hcg) (X := X) (Y := Y) (f := f) (i := i)
    (s₀ := s₀) (hbase := hbase) (B := B) (hB := hB) (U := U) (hU := hU)
    (hcontains := hcontains) (k := k) (hUk := hUk) (s := s) (hs := hs) (hreg := hreg)
    (t := t) (hst := hst) (hregst := hregst) (b := b) x
  have hw := CoefficientWeight.value f.left i.left s₀ hsec
    U hU hcontains s t hst x
  change CoefficientResidueClass.weight f.left i.left s₀ hsec
    U hU hcontains s t hst x = _ at hw
  exact reweight _ _ _ _ hr hw

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.EtalePointPairingData
