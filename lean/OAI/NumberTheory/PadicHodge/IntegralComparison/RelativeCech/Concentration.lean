import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.CoefficientQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.QuasicoherentTruncation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.ConcentrationNaturality

/-! # Concentration -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Concentration

noncomputable section

/-! The canonical sheaf concentration on the actual relative Čech total.
Only affine intersections are needed; no ambient coverage is asserted. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration
variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  (U : X.Opens) (hU : IsAffineOpen U)
  {ι : Type u} [LinearOrder ι] (V : ι → X.Opens) (hV : ∀ i, IsAffineOpen (V i))

def totalFunctor : CochainComplex X.Modules ℕ ⥤ CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ :=
  (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).mapHomologicalComplex (.up ℕ) ⋙
    (Total.localFunctor U V).mapHomologicalComplex (.up ℕ) ⋙
      HomologicalComplex₂.totalFunctor (ModuleCat.{u} Γ(S, ⊤)) (.up ℕ) (.up ℕ) (.up ℕ)

def functor (q : ℕ) : CochainComplex X.Modules ℕ ⥤ ModuleCat.{u} Γ(S, ⊤) :=
  Concentration.totalFunctor π U V ⋙ homologyFunctor (ModuleCat.{u} Γ(S, ⊤)) (.up ℕ) q

variable (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)

include hU hV hK in
theorem projection_isIso (q : ℕ) : IsIso ((functor π U V q).map (CohomologyConcentration.projection K c)) := by
  let (k : ℕ) := QuasicoherentTruncation.truncation K c k
  let := CohomologyConcentration.projection_quasiIso K c hK
  let := CoefficientQuasiIso.quasiIso π U hU V hV (CohomologyConcentration.projection K c)
  change IsIso (homologyMap (Total.sourceMap U V
    (CoefficientQuasiIso.coefficientMap π (CohomologyConcentration.projection K c))) q)
  infer_instance

include hU hV hK in
theorem inclusion_isIso (q : ℕ) : IsIso ((functor π U V q).map (CohomologyConcentration.inclusion K c)) := by
  let (k : ℕ) := QuasicoherentTruncation.truncation K c k
  let := QuasicoherentTruncation.cohomology K c
  let (k : ℕ) := QuasicoherentTruncation.single (K.homology c) c k
  let := CohomologyConcentration.inclusion_quasiIso K c hK
  let := CoefficientQuasiIso.quasiIso π U hU V hV (CohomologyConcentration.inclusion K c)
  change IsIso (homologyMap (Total.sourceMap U V
    (CoefficientQuasiIso.coefficientMap π (CohomologyConcentration.inclusion K c))) q)
  infer_instance

def iso (q : ℕ) := by
  letI := projection_isIso π U hU V hV K c hK q
  letI := inclusion_isIso π U hU V hV K c hK q
  exact Functor.ConcentrationSingle.iso (functor π U V q) K c

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Concentration
