import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.EtalePointPairingData
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.RefinementCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueMapCoordinates

/-! # Etale Point Pairing Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.EtalePointPairingCoordinates

noncomputable section

/-! Every coefficient pairing of the actual finite local point class
is section evaluation times the same original scalar point residue.
The affine basis data are the genuine projective parameter chart. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.Module Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
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

attribute [local instance] EtalePointPairingData.composite_smooth
  EtalePointPairingData.composite_proper EtalePointPairingData.composite_connected
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.EtalePointPairingData

include i hbase in
omit [IsNoetherianRing R] [Module.Injective R R] [Nonempty ↥X.left] [IsFinite (Over.Hom.left f)] [Etale (Over.Hom.left f)] [IsClosedImmersion (Over.Hom.left i)] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom] in
private theorem pointClosed : IsClosedImmersion (s₀ ≫ f.left) := by
  let : Subsingleton (Spec (CommRingCat.of R)) := Ring.KrullDimLE.subsingleton_primeSpectrum R
  exact isClosedImmersion_of_comp_eq_id (i.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (s₀ ≫ f.left)
    (FiniteEtale.SectionUnit.section_over X Y f i s₀ hbase)

local instance coefficientsQC : (Cech.StructurePullbackUnit.coefficients f.left i.left).IsQuasicoherent :=
  Finite.MapPureTrace.coefficients_quasicoherent f.left i.left
local instance coefficientsFinite : (Cech.StructurePullbackUnit.coefficients f.left i.left).IsFiniteType :=
  Finite.MapPureTrace.coefficients_finiteType f.left i.left

abbrev originalValue (x : Finite.FlatCoefficientSections.coefficientRing f.left i.left U) := by
  letI : IsClosedImmersion (s₀ ≫ f.left) := pointClosed
    (X := X) (Y := Y) (f := f) (i := i) (s₀ := s₀) (hbase := hbase)
  exact CoefficientResidueDimensionData.leftMap X f.left i
    (ProjectivePoint.Survivor.chart (R := R) (n := n)) B U hU k hUk s hs hreg t b
    (PrincipalPoint.Fraction.family U t) (c+g) x
    (ProjectivePoint.CoefficientLocalClass.value i.left (s₀ ≫ f.left)
      (FiniteEtale.SectionUnit.section_over X Y f i s₀ hbase) B hB
      (Cech.StructurePullbackUnit.coefficients f.left i.left)
      (Cech.SectionCoefficientUnit.sheafMap s₀ f.left i.left) U hU s t hst hcg)

abbrev residueValue (x : Finite.FlatCoefficientSections.coefficientRing f.left i.left U) := by
  letI : IsClosedImmersion (s₀ ≫ f.left) := pointClosed
    (X := X) (Y := Y) (f := f) (i := i) (s₀ := s₀) (hbase := hbase)
  letI := ProjectiveCoefficient.RefinementCoordinates.nativeLeft_isIso i.left (s₀ ≫ f.left) B hB
    (Cech.StructurePullbackUnit.coefficients f.left i.left)
    (Cech.SectionCoefficientUnit.sheafMap s₀ f.left i.left) U hU
    (PrincipalPoint.Fraction.family U t) (c+g)
  exact (Supported.CechHomotopyEquivalence.functor (PrincipalPoint.Fraction.family U t) (c+g)).map
    (CoefficientResidueDimensionData.symbol (c := c) X i U hU t)
    ((Supported.CechHomotopyEquivalence.functor (PrincipalPoint.Fraction.family U t) (c+g)).map
      (CoefficientResidueMapCoordinates.raw X f.left i B U hU k hUk s hs hreg b x)
      (((Supported.CechHomotopyEquivalence.functor (PrincipalPoint.Fraction.family U t) (c+g)).map
        (ProjectiveCoefficient.RefinementCoordinates.nativeRight i.left (s₀ ≫ f.left) B
          (Cech.StructurePullbackUnit.coefficients f.left i.left)
          (Cech.SectionCoefficientUnit.sheafMap s₀ f.left i.left) U hU) ≫
          inv ((Supported.CechHomotopyEquivalence.functor (PrincipalPoint.Fraction.family U t) (c+g)).map
            (ProjectiveCoefficient.RefinementCoordinates.nativeLeft i.left (s₀ ≫ f.left) B
              (Cech.StructurePullbackUnit.coefficients f.left i.left)
              (Cech.SectionCoefficientUnit.sheafMap s₀ f.left i.left) U hU)))
        (ProjectivePoint.LocalCoordinates.pointAt i.left (s₀ ≫ f.left)
          (FiniteEtale.SectionUnit.section_over X Y f i s₀ hbase) B hB U hU s t hst hcg)))

omit [SmoothOfRelativeDimension g X.hom] in
omit [Nonempty ↥X.left] [Etale (Over.Hom.left f)] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom] in
theorem image (x : Finite.FlatCoefficientSections.coefficientRing f.left i.left U) :
    originalValue (hcg := hcg) (X := X) (Y := Y) (f := f) (i := i)
      (s₀ := s₀) (hbase := hbase) (B := B) (hB := hB) (U := U) (hU := hU)
      (k := k) (hUk := hUk) (s := s) (hs := hs) (hreg := hreg) (t := t) (hst := hst) (b := b) x =
      residueValue (hcg := hcg) (X := X) (Y := Y) (f := f) (i := i)
      (s₀ := s₀) (hbase := hbase) (B := B) (hB := hB) (U := U) (hU := hU)
      (k := k) (hUk := hUk) (s := s) (hs := hs) (hreg := hreg) (t := t) (hst := hst) (b := b) x := by
  let : IsClosedImmersion (s₀ ≫ f.left) := pointClosed
    (X := X) (Y := Y) (f := f) (i := i) (s₀ := s₀) (hbase := hbase)
  have h := ProjectiveCoefficient.RefinementCoordinates.comparison i.left (s₀ ≫ f.left)
    (FiniteEtale.SectionUnit.section_over X Y f i s₀ hbase) B hB
    (Cech.StructurePullbackUnit.coefficients f.left i.left)
    (Cech.SectionCoefficientUnit.sheafMap s₀ f.left i.left) U hU s t hst hcg
    (CoefficientResidueMapCoordinates.raw X f.left i B U hU k hUk s hs hreg b x)
  have hm := congrArg
    ((Supported.CechHomotopyEquivalence.functor (PrincipalPoint.Fraction.family U t) (c+g)).map
      (CoefficientResidueDimensionData.symbol (c := c) X i U hU t)) h
  simpa only [originalValue, residueValue, CoefficientResidueDimensionData.leftMap,
    ConcreteCategory.comp_apply, CoefficientResidueMapCoordinates.native_eq] using hm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.EtalePointPairingCoordinates
