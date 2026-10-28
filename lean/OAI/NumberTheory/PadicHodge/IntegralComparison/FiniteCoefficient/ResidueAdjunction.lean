import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.ResiduePullback
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.HomEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PushforwardSectionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionTransformationAtOne
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LocalQuasiIso

/-! # Residue Adjunction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.ResidueAdjunction

noncomputable section

/-! Evaluation of the original finite coefficient adjunction agrees on
all principal opens with coefficient residue followed by the same local form. -/
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
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.ResidueAdjunction.ambientRing U
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
  (P : ProjectiveResolution (ModuleCat.of Γ(Z, U) (Finite.FlatCoefficientSections.coefficientRing f i U)))
  (V : X.Modules) [V.IsQuasicoherent] (ω : Γ(V, i ⁻¹ᵁ U))
  (κ : (Affine.LinearResolutionPurity.internalComplex N K).homology c ⟶
    (Scheme.Modules.pushforward i).obj V)
  (φ : (Affine.LinearResolutionPurity.internalComplex N L).homology c ⟶
    ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (Cech.StructurePullbackUnit.coefficients f i) ((Scheme.Modules.pushforward i).obj V))
  (x : Finite.FlatCoefficientSections.coefficientRing f i U)
  (hκ : (Affine.ModuleExactSections.sections U).map κ =
    PrincipalResidue.SurvivorSection.sectionMap U hU N e K i ε s hs hreg ≫
      Principal.PushforwardSectionCoordinates.sectionsMap i U V ω)
  (hφ : ∀ z, ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen (Cech.StructurePullbackUnit.coefficients f i) ((Scheme.Modules.pushforward i).obj V) U (φ.app U z) x =
    κ.app U (Affine.CoefficientRestriction.pullback U hU N K L (Principal.ClosedQuotient.directImage i) (Cech.StructurePullbackUnit.coefficients f i) ε ε'
      (Finite.FlatCoefficientSections.quotientRing i U) (Finite.FlatCoefficientSections.coefficientRing f i U)
      (RestrictionNormalization.scalarChartIso i U hU)
      (Finite.FlatCoefficientSections.chartIso f i U hU) c z x))

include hκ hφ in
theorem comparison :
    letI := QuotientAction.algebra f i U hU s hs
    letI := QuotientAction.tower f i U hU s hs
    (Principal.ModuleFunctor.functor U hU).map φ ≫
      Principal.HomEvaluation.map U hU MC ((Scheme.Modules.pushforward i).obj V) x =
    Principal.CoefficientResidueSurvivor.survivor U hU N e MC L ε'
      (ModuleCat.of A (Finite.FlatCoefficientSections.coefficientRing f i U)) (Finite.FlatCoefficientSections.chartIso f i U hU) P i s hs hreg
      (Koszul.CoefficientPointFraction.vector A s (Finite.FlatCoefficientSections.coefficientRing f i U) x) ≫
      Principal.PushforwardSection.map i U hU V ω := by
  let := QuotientAction.algebra f i U hU s hs
  let := QuotientAction.tower f i U hU s hs
  let D := (Affine.LinearResolutionPurity.internalComplex N L).homology c
  let F := (Scheme.Modules.pushforward i).obj V
  let a := (Principal.AtOne.iso U hU).app D
  let aF := (Principal.AtOne.iso U hU).app F
  let β := Koszul.CoefficientPointFraction.vector A s (Finite.FlatCoefficientSections.coefficientRing f i U) x
  let Q := ResiduePullback.scalarResolution i U hU K ε s hs
  let u := Principal.CoefficientResidueSurvivor.survivor U hU N e MC L ε'
    (ModuleCat.of A (Finite.FlatCoefficientSections.coefficientRing f i U)) (Finite.FlatCoefficientSections.chartIso f i U hU) P i s hs hreg β
  let u₀ := Principal.CoefficientResidueSurvivor.sectionMap U hU N e MC L ε'
    (ModuleCat.of A (Finite.FlatCoefficientSections.coefficientRing f i U)) (Finite.FlatCoefficientSections.chartIso f i U hU) i s hs hreg β Q
  let : D.IsQuasicoherent := Affine.LocalQuasiIso.homology_quasicoherent
    (Affine.LinearResolutionPurity.internalComplex N L) c
  let : F.IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom i
  apply Principal.SectionTransformationAtOne.Ext.ext_atOne U hU D F
  apply (cancel_epi a.hom).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  have hn := ConcreteCategory.congr_hom ((Principal.AtOne.iso U hU).hom.naturality φ).symm z
  have he := Principal.HomEvaluation.atOne U hU MC F x (φ.app U z)
  have hp := ResiduePullback.section f i U hU K L ε ε' N e s hs hreg z x
  have hk := ConcreteCategory.congr_hom hκ
    (Affine.CoefficientRestriction.pullback U hU N K L (Principal.ClosedQuotient.directImage i) (Cech.StructurePullbackUnit.coefficients f i) ε ε'
      (Finite.FlatCoefficientSections.quotientRing i U) (Finite.FlatCoefficientSections.coefficientRing f i U)
      (RestrictionNormalization.scalarChartIso i U hU)
      (Finite.FlatCoefficientSections.chartIso f i U hU) c z x)
  have hl : ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen MC F U (φ.app U z) x =
      Principal.PushforwardSectionCoordinates.sectionsMap i U V ω (u₀ z) :=
    (hφ z).trans (hk.trans (congrArg (Principal.PushforwardSectionCoordinates.sectionsMap i U V ω) hp.symm))
  have hu := ConcreteCategory.congr_hom
    (Principal.CoefficientResidueSurvivor.atOne U hU N e MC L ε'
      (ModuleCat.of A (Finite.FlatCoefficientSections.coefficientRing f i U)) (Finite.FlatCoefficientSections.chartIso f i U hU) P i s hs hreg β Q) z
  have hv := Principal.PushforwardSection.atOne i U hU V ω (u₀ z)
  change (Principal.HomEvaluation.map U hU MC F x).app (op (Principal.AtOne.object U))
      (((Principal.ModuleFunctor.functor U hU).map φ).app (op (Principal.AtOne.object U))
        (a.hom z)) =
    (Principal.PushforwardSection.map i U hU V ω).app (op (Principal.AtOne.object U))
      (u.app (op (Principal.AtOne.object U)) (a.hom z))
  exact (congrArg ((Principal.HomEvaluation.map U hU MC F x).app
      (op (Principal.AtOne.object U))) hn).trans
    (he.trans ((congrArg aF.hom hl).trans
      (hv.symm.trans (congrArg ((Principal.PushforwardSection.map i U hU V ω).app
        (op (Principal.AtOne.object U))) hu.symm))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.ResidueAdjunction
