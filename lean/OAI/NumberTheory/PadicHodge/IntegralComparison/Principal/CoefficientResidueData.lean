import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ResolutionAtOneCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientNormalPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientEvaluationHomotopy
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.AtOne

/-! # Coefficient Residue Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientResidueData

noncomputable section

/-! The original coefficient resolution, evaluated at a normal-quotient
vector, gives a map to the actual closed structure sheaf on principal opens. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
  (N : Y.Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(Y, U)] Γ(Y, U))
  (M : Y.Modules) [M.IsQuasicoherent]
  (K : ChainComplex Y.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ Y.Modules).obj M) [QuasiIso ε]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  (T : ModuleCat.{u} Γ(Y, U)) (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ T)
  (P : ProjectiveResolution T)
  {X : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
  {c : ℕ} (s : Fin c → Γ(Y, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Y, U) s = f.ker.ideal ⟨U, hU⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn s))
  (β : ModuleCat.of Γ(Y, U)
    (Γ(Y, U) ⧸ KoszulPartial.Resolution.normalIdeal Γ(Y, U) s) ⟶ T)

abbrev coefficientResolution := Resolution.Comparison.resolution U hU M K ε T eM
abbrev comparisonLift := ResolutionAtOneCoordinates.lift U hU M K ε T eM P
abbrev normalLift := ProjectiveResolution.lift β
  (KoszulPartial.Resolution.normalResolution Γ(Y, U) s hreg) P

abbrev evaluation := Koszul.CoefficientEvaluationHomotopy.evaluation Γ(Y, U)
  (SectionPresheaf.rings U hU) s hreg T P (normalLift U T P s hreg β)

def map : Koszul.Comparison.nativeComplex U hU N K ⟶
    (single ((SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat Γ(Y, U)) (.up ℕ) c).obj
      (ClosedKoszulResidue.target f U hU) :=
  (Resolution.Comparison.equivalence U hU N e M K ε T eM P).hom ≫
    evaluation U hU T P s hreg β ≫ ClosedKoszulResidue.residue f U hU s hs

def normalizedMap :
    (((AffineOpen.LinearHom.sectionHom U N).mapHomologicalComplex (.up ℕ)).obj K.op) ⟶
      (single (ModuleCat Γ(Y, U)) (.up ℕ) c).obj
        (ModuleCat.of Γ(Y, U) (Γ(Y, U) ⧸ KoszulPartial.Resolution.normalIdeal Γ(Y, U) s)) :=
  (OrientedResidueNormalizationBase.sourceAtOneIso U hU N K).hom ≫
    ((OrientedResidueNormalization.atOneFunctor U).mapHomologicalComplex (.up ℕ)).map
      (CoefficientResidueData.map U hU N e M K ε T eM P f s hs hreg β) ≫
    (singleMapHomologicalComplex
      (OrientedResidueNormalization.atOneFunctor U) (.up ℕ) c).hom.app
        (ClosedKoszulResidue.target f U hU) ≫
    (single (ModuleCat Γ(Y, U)) (.up ℕ) c).map
      (OrientedResidueNormalization.targetAtOne U hU f s hs).hom

def canonicalMap :
    (((AffineOpen.LinearHom.sectionHom U N).mapHomologicalComplex (.up ℕ)).obj K.op) ⟶
      (single (ModuleCat Γ(Y, U)) (.up ℕ) c).obj
        (ModuleCat.of Γ(Y, U) (Γ(Y, U) ⧸ KoszulPartial.Resolution.normalIdeal Γ(Y, U) s)) :=
  (OrientedResidueNormalizationBase.affineDualIso U hU N e K).hom ≫
    DualComplexHomology.map Γ(Y, U) (comparisonLift U hU M K ε T eM P) ≫
    Koszul.CoefficientNormalPurity.map Γ(Y, U) s hreg P β

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientResidueData
