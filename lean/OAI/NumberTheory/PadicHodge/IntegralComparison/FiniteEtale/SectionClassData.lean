import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SectionUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.UnitPureClass

/-! # Section Class Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SectionClassData

noncomputable section

/-! The original fixed point class for the actual finite coefficient
quotient, followed by its original pure cohomology and adjunction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  [IsArtinianRing R] [IsLocalRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (X Y : Over (Spec (CommRingCat.of R))) [Nonempty X.left] (f : Y ⟶ X)
  [IsFinite f.left] [Etale f.left]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)) [IsClosedImmersion i.left]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  [IsProper Y.hom] [Smooth Y.hom] [GeometricallyConnected Y.hom]
  (s : Spec (CommRingCat.of R) ⟶ Y.left) (hs : s ≫ Y.hom = 𝟙 _)
  (B : ℕ) (hB : n + 2 ≤ B) (g : ℕ) [SmoothOfRelativeDimension g X.hom]

attribute [local instance] ProperTraceBase.composite_dimension

local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.StructurePullbackUnit.coefficients f.left i.left
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SectionClass.point i.left (s ≫ f.left)
local notation "hn" => Fintype.card_fin (n + 2)
local notation "π" => OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 2))
local notation "hsec" => OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SectionUnit.section_over X Y f i s hs
local notation "eM" => OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SectionUnit.coefficientUnit X Y f i s hs
local notation "eP" => OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SectionClass.pointUnitIso i.left (s ≫ f.left) hsec
local notation "q" => OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.SectionCoefficientUnit.sheafMap s f.left i.left
local notation "hPure" => OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.MapCoefficientPurity.exactAt f.left i.left B n hn hB g
local notation "hdeg" => OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.ProperTraceBase.degree X i g

local instance coefficient_qc : (M).IsQuasicoherent :=
  Finite.MapPureTrace.coefficients_quasicoherent f.left i.left

local instance coefficient_finite : (M).IsFiniteType :=
  Finite.MapPureTrace.coefficients_finiteType f.left i.left

def pureClass := by
  letI : Subsingleton (Spec (.of R)) := Ring.KrullDimLE.subsingleton_primeSpectrum R
  letI : IsClosedImmersion (s ≫ f.left) :=
    isClosedImmersion_of_comp_eq_id (i.left ≫ π) (s ≫ f.left) hsec
  letI : (P).IsQuasicoherent := Finite.MapPureTrace.coefficients_quasicoherent (s ≫ f.left) i.left
  letI : (P).IsFiniteType := Finite.MapPureTrace.coefficients_finiteType (s ≫ f.left) i.left
  exact Projective.UnitPureClass.pureClass M P B n hn hB q eM eP (n + 1 - g) hPure g hdeg

def sectionClass : ProperTraceBase.cohomology X Y f i g :=
  (ProjectiveRefinement.Serre.cohomologyFunctor (R := R) (σ := Fin (n + 2)) g).map
    (ProjectiveFinite.EtaleAdjunction.iso X Y f i g
      (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B hB (ProperTraceBase.dimension_le X i g)).hom
    (pureClass X Y f i s hs B hB g)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SectionClassData
