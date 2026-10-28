import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.VectorCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CoefficientCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientResidueSurvivor

/-! # Residue Pullback -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.ResiduePullback

noncomputable section

/-! The coefficient residue and the original finite adjunction use the
same affine pullback, including the literal closed-scheme scalar coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
attribute [local instance] Finite.FlatCoefficientSections.quotientAlgebra Finite.FlatCoefficientSections.coefficientAlgebra Finite.FlatCoefficientSections.ambientAlgebra
attribute [local instance] Principal.OrientedResidue.structure_quasicoherent
variable {Y X Z : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
  (i : X ⟶ Z) [IsClosedImmersion i] (U : Z.Opens) (hU : IsAffineOpen U)

local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedQuotient.directImage i
local notation "MC" => OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.StructurePullbackUnit.coefficients f i
private abbrev ambientRing := Γ(Z, U)
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.ResiduePullback.ambientRing U
local instance coefficient_qc : (MC).IsQuasicoherent :=
  Finite.MapPureTrace.coefficients_quasicoherent f i

variable (K L : ChainComplex Z.Modules ℕ)
  [∀ q, (K.X q).IsQuasicoherent] [∀ q, (L.X q).IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ Z.Modules).obj (Principal.ClosedQuotient.directImage i)) [QuasiIso ε]
  (ε' : L ⟶ (ChainComplex.single₀ Z.Modules).obj (Cech.StructurePullbackUnit.coefficients f i)) [QuasiIso ε']
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (L.X q))]
  (N : Z.Modules) [N.IsQuasicoherent] (e : Γ(N, U) ≃ₗ[Γ(Z, U)] Γ(Z, U))
  [∀ q, ((Affine.LinearResolutionPurity.internalComplex N K).X q).IsQuasicoherent]
  [∀ q, ((Affine.LinearResolutionPurity.internalComplex N L).X q).IsQuasicoherent]
  {c : ℕ} (s : Fin c → Γ(Z, U))
  (hs : KoszulPartial.Resolution.normalIdeal Γ(Z, U) s = i.ker.ideal ⟨U, hU⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Z, U) (List.ofFn s))

abbrev scalarResolution := Affine.OrientedPurity.resolution U hU K M ε
  (KoszulPartial.Resolution.normalIdeal A s) (Principal.OrientedResidue.quotientIso i U hU s hs)

local notation "PC" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientResidueData.coefficientResolution U hU MC L ε'
  (ModuleCat.of A (Finite.FlatCoefficientSections.coefficientRing f i U)) (Finite.FlatCoefficientSections.chartIso f i U hU)
private abbrev lineSections := (AffineOpen.InternalHom.sections U hU).obj N
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CohomologyMaps.homFunctor A (OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.ResiduePullback.lineSections U hU N)

omit [N.IsQuasicoherent] in
 theorem «section» (z : Γ((Affine.LinearResolutionPurity.internalComplex N L).homology c, U))
    (x : Finite.FlatCoefficientSections.coefficientRing f i U) :
    letI := QuotientAction.algebra f i U hU s hs
    letI := QuotientAction.tower f i U hU s hs
    Principal.CoefficientResidueSurvivor.sectionMap U hU N e MC L ε'
      (ModuleCat.of A (Finite.FlatCoefficientSections.coefficientRing f i U)) (Finite.FlatCoefficientSections.chartIso f i U hU) i s hs hreg
      (Koszul.CoefficientPointFraction.vector A s (Finite.FlatCoefficientSections.coefficientRing f i U) x)
      (scalarResolution i U hU K ε s hs) z =
    PrincipalResidue.SurvivorSection.sectionMap U hU N e K i ε s hs hreg
      (Affine.CoefficientRestriction.pullback U hU N K L (Principal.ClosedQuotient.directImage i) (Cech.StructurePullbackUnit.coefficients f i) ε ε'
        (Finite.FlatCoefficientSections.quotientRing i U) (Finite.FlatCoefficientSections.coefficientRing f i U)
        (RestrictionNormalization.scalarChartIso i U hU)
        (Finite.FlatCoefficientSections.chartIso f i U hU) c z x) := by
  let := QuotientAction.algebra f i U hU s hs
  let := QuotientAction.tower f i U hU s hs
  have hm := Resolution.CoefficientCoordinates.map F
    (AffineOpen.Resolution.ofAugmentation U hU M K ε) PC
    (Principal.OrientedResidue.quotientIso i U hU s hs)
    (RestrictionNormalization.scalarChartIso i U hU)
    (Koszul.CoefficientPointFraction.vector A s (Finite.FlatCoefficientSections.coefficientRing f i U) x)
    (Quotient.CoefficientEvaluation.point A (Finite.FlatCoefficientSections.quotientRing i U) (Finite.FlatCoefficientSections.coefficientRing f i U) x)
    (VectorCoordinates.vector f i U hU s hs x) c
  have hp := Affine.CoefficientRestriction.comparison_pullback U hU N K L M MC ε ε'
    (Finite.FlatCoefficientSections.quotientRing i U) (Finite.FlatCoefficientSections.coefficientRing f i U)
    (RestrictionNormalization.scalarChartIso i U hU)
    (Finite.FlatCoefficientSections.chartIso f i U hU) c z x
  have hc := ConcreteCategory.congr_hom hm
    ((AffinePrincipal.Cohomology.Comparison.comparison U hU N L c).hom z)
  have h := hp.trans hc.symm
  dsimp only [Principal.CoefficientResidueSurvivor.sectionMap, PrincipalResidue.SurvivorSection.sectionMap,
    Affine.OrientedPurity.iso, AffinePrincipal.Cohomology.Comparison.comparison,
    Iso.trans_hom, homologyMapIso_hom, ConcreteCategory.comp_apply]
  apply congrArg ((PrincipalResidue.SurvivorSection.coefficientIso U hU i s hs).inv)
  apply congrArg ((LinearHomOrientedPurity.iso A
    (KoszulPartial.Resolution.normalIdeal A s) s rfl hreg
    (scalarResolution i U hU K ε s hs) ((AffineOpen.InternalHom.sections U hU).obj N)
    (Principal.OrientedResidueNormalizationBase.lineIso U hU N e)).hom)
  exact h.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.ResiduePullback
