import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SectionClassData

/-! # Section Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SectionClass

noncomputable section

/-! The finite coefficient class has trace one under the original
proper source trace, with the original target projective embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality

private theorem replace_unit {A B : Type*} [One B] (F : A → B)
    {a b : A} (h : a = b) (hF : F a = 1) : F b = 1 := h ▸ hF

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

local instance coefficient_qc' : (M).IsQuasicoherent :=
  Finite.MapPureTrace.coefficients_quasicoherent f.left i.left

local instance coefficient_finite' : (M).IsFiniteType :=
  Finite.MapPureTrace.coefficients_finiteType f.left i.left

omit [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] in
theorem coefficient_trace_one :
    ProperTraceBase.coefficientTrace X Y f i B hB g
      (SectionClassData.pureClass X Y f i s hs B hB g) = 1 := by
  let : Subsingleton (Spec (.of R)) := Ring.KrullDimLE.subsingleton_primeSpectrum R
  let : IsClosedImmersion (s ≫ f.left) :=
    isClosedImmersion_of_comp_eq_id (i.left ≫ π) (s ≫ f.left) hsec
  let : (P).IsQuasicoherent := Finite.MapPureTrace.coefficients_quasicoherent (s ≫ f.left) i.left
  let : (P).IsFiniteType := Finite.MapPureTrace.coefficients_finiteType (s ≫ f.left) i.left
  have h := Projective.UnitPureClass.trace_one M P B n hn hB q eM eP
    (SectionUnit.unit_preserved X Y f i s hs)
    (n + 1 - g) hPure g hdeg
  exact replace_unit
    (fun v => SerreUnitTrace.trace (Projective.TopTracePairing.coefficientRing R)
      (ProperTraceBase.coefficientPairing X Y f i B hB g) v
      (SectionClassData.pureClass X Y f i s hs B hB g))
    (SectionUnit.coefficientUnit_one X Y f i s hs) h

omit [Smooth X.hom] [GeometricallyConnected X.hom] in
theorem trace_one :
    ProperTraceBase.trace X Y f i B hB g
      (SectionClassData.sectionClass X Y f i s hs B hB g) = 1 := by
  let H := ProjectiveRefinement.Serre.cohomologyFunctor (R := R) (σ := Fin (n + 2)) g
  let e := ProjectiveFinite.EtaleAdjunction.iso X Y f i g
    (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B hB (ProperTraceBase.dimension_le X i g)
  let x := SectionClassData.pureClass X Y f i s hs B hB g
  have hx := ConcreteCategory.congr_hom (H.mapIso e).hom_inv_id x
  change H.map e.inv (H.map e.hom x) = x at hx
  change ProperTraceBase.coefficientTrace X Y f i B hB g
    (H.map e.inv (H.map e.hom x)) = 1
  rw [hx]
  exact coefficient_trace_one X Y f i s hs B hB g

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SectionClass
