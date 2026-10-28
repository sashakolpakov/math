import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedInternalHom
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.PresheafTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections

/-! # Finite Etale Trace Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleTraceCoordinates

noncomputable section

/-! The original ambient principal Hom diagram has finite-etale trace
tensor coordinates over the actual closed-scheme section ring. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
variable {Y X Z : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
  (i : X ⟶ Z) [IsClosedImmersion i] (U : Z.Opens) (hU : IsAffineOpen U)
  (N : X.Modules)
private abbrev ambientRing := Γ(Z, U)
private abbrev scalarRestriction := ModuleCat.restrictScalars (i.app U).hom
private abbrev coefficientModule :=
  (Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleTraceCoordinates.ambientRing U
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U
local notation "B" => OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f i U
local notation "C" => (OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf.Index U)ᵒᵖ
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedScalars.modules i U hU N
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleTraceCoordinates.scalarRestriction i U
local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleTraceCoordinates.coefficientModule f
local instance coefficientStructure :
    Algebra (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f i U) := IntegralComparison.Finite.FlatCoefficientSections.coefficientAlgebra f i U
local instance coefficient_qc : (M).IsQuasicoherent := by
  let : (SheafOfModules.unit Y.ringCatSheaf).IsQuasicoherent :=
    AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.isInvertible_unit
  exact AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f

variable [hfree : Module.Free (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f i U)]
  [hfinite : Module.Finite (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f i U)]
  [hetale : Algebra.Etale (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f i U)]

def forget : (C ⥤ ModuleCat.{u} Q) ⥤ (C ⥤ ModuleCat.{u} A) :=
  (Functor.whiskeringRight C (ModuleCat.{u} Q) (ModuleCat.{u} A)).obj G

include hfree hfinite hetale in
def iso : SectionPresheaf.modules U hU
    (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule ((Scheme.Modules.pushforward i).obj M)
      ((Scheme.Modules.pushforward i).obj N)) ≅
    FiniteEtale.PresheafTrace.tensor Q B P ⋙ G :=
  ClosedInternalHom.iso i U hU M N ≪≫
    (forget i U).mapIso (FiniteEtale.PresheafTrace.duality Q B P).symm

include hfree hfinite hetale in
theorem pairing (x : IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f i U) :
    (iso f i U hU N).hom ≫
      (forget i U).map (FiniteEtale.PresheafTrace.pairing Q B P x) ≫
      (ClosedScalars.restrictionIso i U hU N).hom =
    HomEvaluation.map U hU ((Scheme.Modules.pushforward i).obj M)
      ((Scheme.Modules.pushforward i).obj N) x := by
  calc
    _ = (ClosedInternalHom.iso i U hU M N).hom ≫
        (forget i U).map ((FiniteEtale.PresheafTrace.duality Q B P).inv ≫
          FiniteEtale.PresheafTrace.pairing Q B P x) ≫
        (ClosedScalars.restrictionIso i U hU N).hom := by
      simp only [iso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
        Functor.map_comp, Category.assoc]
    _ = (ClosedInternalHom.iso i U hU M N).hom ≫
        (forget i U).map (HomPresheafDualFrame.evaluation Q P (ModuleCat.of Q B) x) ≫
        (ClosedScalars.restrictionIso i U hU N).hom := by
      rw [FiniteEtale.PresheafTrace.pairing, Iso.inv_hom_id_assoc]
    _ = _ := ClosedInternalHom.evaluation i U hU M N x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleTraceCoordinates
