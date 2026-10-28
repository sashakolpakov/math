import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.Concentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdditiveSectionsNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AmbientProducts
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.TerminalScalars
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.AdditiveCechConcentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.AmbientTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.ConcentrationMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConcentrationLocalRecovery

/-! # Relative Concentration -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeConcentration

noncomputable section

/-! The genuine affine principal concentration is the same concentration
on its ambient relative Čech diagram, after forgetting the affine scalar ring. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdditiveSectionsNaturality OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration
variable {X : Scheme.{u}} [X.IsSeparated] (U : X.Opens) (hU : IsAffineOpen U)
  {ι : Type u} [LinearOrder ι] (W : ι → SectionPresheaf.Index U)

abbrev ambient := (AdditiveSections.opens U hU).obj (⊤_ SectionPresheaf.Index U)
abbrev family := (AdditiveSections.opens U hU).obj ∘ W

include hU in
omit [X.IsSeparated] in
theorem ambient_affine : IsAffineOpen (ambient U hU) := by
  change IsAffineOpen (SectionPresheaf.openSubset U (⊤_ SectionPresheaf.Index U))
  rw [TerminalScalars.open_eq U hU]
  exact hU

include hU in
omit [X.IsSeparated] [LinearOrder ι] in
theorem family_affine (i : ι) : IsAffineOpen (family U hU W i) :=
  hU.basicOpen (W i).val

abbrev linearFunctor (q : ℕ) :=
  PrincipalReference.Concentration.Reference.functor U hU W q ⋙ AdditiveSections.forgetScalars U
abbrev relativeFunctor (q : ℕ) :=
  Relative.AdditiveCechConcentration.functor (ambient U hU) (family U hU W) q

abbrev coefficients (K : CochainComplex X.Modules ℕ) :=
  Relative.AdditiveCechConcentration.coefficients K

def comparison (K : CochainComplex X.Modules ℕ) (q : ℕ) :
    (linearFunctor U hU W q).obj K ≅ (relativeFunctor U hU W q).obj K :=
  AdditiveSections.homologyIso U hU K W q ≪≫
    homologyMapIso (AugmentedCech.AmbientTotal.totalIso (AdditiveSections.opens U hU) W (coefficients K)) q

omit [X.IsSeparated] in
theorem naturality {K L : CochainComplex X.Modules ℕ} (a : K ⟶ L) (q : ℕ) :
    (linearFunctor U hU W q).map a ≫ (comparison U hU W L q).hom =
      (comparison U hU W K q).hom ≫ (relativeFunctor U hU W q).map a := by
  have h := congrArg (fun f => homologyMap f q)
    (AugmentedCech.AmbientTotal.naturality (AdditiveSections.opens U hU) W (coefficients K)
      (Relative.AdditiveCechConcentration.coefficientMap a))
  rw [homologyMap_comp, homologyMap_comp] at h
  exact DualComplexHomology.compose_squares _ _ _ _ _ _ _
    (AdditiveSectionsNaturality.homologyIso_naturality U hU a W q) h

variable (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)

abbrev relativeIso (q : ℕ) :=
  Relative.AdditiveCechConcentration.iso (ambient U hU) (ambient_affine U hU)
    (family U hU W) (family_affine U hU W) K c hK q

theorem concentration (q : ℕ) :
    ((AdditiveSections.forgetScalars U).mapIso (PrincipalReference.Concentration.Reference.iso U hU W K c hK q)).hom ≫
      (comparison U hU W ((single X.Modules (.up ℕ) c).obj (K.homology c)) q).hom =
    (comparison U hU W K q).hom ≫ (relativeIso U hU W K c hK q).hom := by
  let := PrincipalReference.Concentration.Reference.projection_isIso U hU W K c hK q
  let := PrincipalReference.Concentration.Reference.inclusion_isIso U hU W K c hK q
  let : IsIso ((linearFunctor U hU W q).map (CohomologyConcentration.projection K c)) := by
    change IsIso ((AdditiveSections.forgetScalars U).map
      ((PrincipalReference.Concentration.Reference.functor U hU W q).map (CohomologyConcentration.projection K c)))
    infer_instance
  let : IsIso ((linearFunctor U hU W q).map (CohomologyConcentration.inclusion K c)) := by
    change IsIso ((AdditiveSections.forgetScalars U).map
      ((PrincipalReference.Concentration.Reference.functor U hU W q).map (CohomologyConcentration.inclusion K c)))
    infer_instance
  let := Relative.AdditiveCechConcentration.projection_isIso (ambient U hU) (ambient_affine U hU)
    (family U hU W) (family_affine U hU W) K c hK q
  let := Relative.AdditiveCechConcentration.inclusion_isIso (ambient U hU) (ambient_affine U hU)
    (family U hU W) (family_affine U hU W) K c hK q
  have h := ConcentrationLocalRecovery.square (linearFunctor U hU W q)
    (relativeFunctor U hU W q) K c
    (comparison U hU W K q).hom (comparison U hU W (CohomologyConcentration.truncation K c) q).hom
    (comparison U hU W ((single X.Modules (.up ℕ) c).obj (K.homology c)) q).hom
    (naturality U hU W (CohomologyConcentration.projection K c) q) (naturality U hU W (CohomologyConcentration.inclusion K c) q)
  rw [← Functor.ConcentrationMap.iso_map] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeConcentration
