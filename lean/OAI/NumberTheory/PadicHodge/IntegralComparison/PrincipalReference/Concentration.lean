import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ModuleQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.ConcentrationForget
import OAI.NumberTheory.PadicHodge.IntegralComparison.QuasicoherentTruncation

/-! # Concentration -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.Concentration.Reference

noncomputable section

/-! Principal supported concentration using the original sheaf
projection and inclusion, so its surviving sheaf is unchanged. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  {ι : Type u} [LinearOrder ι] (W : ι → Principal.SectionPresheaf.Index U)

def functor (q : ℕ) : CochainComplex X.Modules ℕ ⥤ ModuleCat.{u} Γ(X, U) :=
  (Principal.ModuleFunctor.functor U hU).mapHomologicalComplex (.up ℕ) ⋙
    Supported.CechHomotopyEquivalence.functor W q

def ambientFunctor (q : ℕ) : CochainComplex X.Modules ℕ ⥤ ModuleCat.{u} Γ(X, U) :=
  (Principal.ModuleFunctor.functor U hU).mapHomologicalComplex (.up ℕ) ⋙
    Supported.ConcentrationForget.ambientFunctor q

def forget (q : ℕ) : functor U hU W q ⟶ ambientFunctor U hU q :=
  Functor.whiskerLeft ((Principal.ModuleFunctor.functor U hU).mapHomologicalComplex (.up ℕ))
    (Supported.ConcentrationForget.forgetTransformation W q)

variable {K L : CochainComplex X.Modules ℕ}
  [∀ q, (K.X q).IsQuasicoherent] [∀ q, (L.X q).IsQuasicoherent]
  (a : K ⟶ L) [QuasiIso a]

theorem supported_isIso (q : ℕ) : IsIso ((functor U hU W q).map a) := by
  let := Principal.ModuleQuasiIso.quasiIso U hU a
  let := AugmentedOrdered.CechQuasiIso.quasiIso W Γ(X, U)
    (((Principal.ModuleFunctor.functor U hU).mapHomologicalComplex (.up ℕ)).map a)
  change IsIso (homologyMap (AugmentedOrdered.CechForgetNaturality.map W
    (((Principal.ModuleFunctor.functor U hU).mapHomologicalComplex (.up ℕ)).map a)) q)
  infer_instance

theorem ambient_isIso (q : ℕ) : IsIso ((ambientFunctor U hU q).map a) := by
  let := Principal.ModuleQuasiIso.quasiIso U hU a
  let : QuasiIso (AugmentedOrdered.CechForgetNaturality.ambientMap
      (((Principal.ModuleFunctor.functor U hU).mapHomologicalComplex (.up ℕ)).map a)) := by
    dsimp only [AugmentedOrdered.CechForgetNaturality.ambientMap]
    infer_instance
  change IsIso (homologyMap
    (AugmentedOrdered.CechForgetNaturality.ambientMap
      (((Principal.ModuleFunctor.functor U hU).mapHomologicalComplex (.up ℕ)).map a)) q)
  infer_instance

variable (K) (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)

include hK in
theorem projection_isIso (q : ℕ) : IsIso ((functor U hU W q).map (CohomologyConcentration.projection K c)) := by
  let (k : ℕ) := QuasicoherentTruncation.truncation K c k
  let := CohomologyConcentration.projection_quasiIso K c hK
  exact supported_isIso U hU W (CohomologyConcentration.projection K c) q

include hK in
theorem inclusion_isIso (q : ℕ) : IsIso ((functor U hU W q).map (CohomologyConcentration.inclusion K c)) := by
  let (k : ℕ) := QuasicoherentTruncation.truncation K c k
  let := QuasicoherentTruncation.cohomology K c
  let (k : ℕ) := QuasicoherentTruncation.single (K.homology c) c k
  let := CohomologyConcentration.inclusion_quasiIso K c hK
  exact supported_isIso U hU W (CohomologyConcentration.inclusion K c) q

include hK in
theorem ambient_projection_isIso (q : ℕ) : IsIso ((ambientFunctor U hU q).map (CohomologyConcentration.projection K c)) := by
  let (k : ℕ) := QuasicoherentTruncation.truncation K c k
  let := CohomologyConcentration.projection_quasiIso K c hK
  exact ambient_isIso U hU (CohomologyConcentration.projection K c) q

include hK in
theorem ambient_inclusion_isIso (q : ℕ) : IsIso ((ambientFunctor U hU q).map (CohomologyConcentration.inclusion K c)) := by
  let (k : ℕ) := QuasicoherentTruncation.truncation K c k
  let := QuasicoherentTruncation.cohomology K c
  let (k : ℕ) := QuasicoherentTruncation.single (K.homology c) c k
  let := CohomologyConcentration.inclusion_quasiIso K c hK
  exact ambient_isIso U hU (CohomologyConcentration.inclusion K c) q

def iso (q : ℕ) := by
  letI := projection_isIso U hU W K c hK q
  letI := inclusion_isIso U hU W K c hK q
  exact IntegralComparison.Functor.ConcentrationSingle.iso (functor U hU W q) K c

def ambientIso (q : ℕ) := by
  letI := ambient_projection_isIso U hU K c hK q
  letI := ambient_inclusion_isIso U hU K c hK q
  exact IntegralComparison.Functor.ConcentrationSingle.iso (ambientFunctor U hU q) K c

theorem square (q : ℕ) : (iso U hU W K c hK q).hom ≫
    (forget U hU W q).app ((single X.Modules (.up ℕ) c).obj (K.homology c)) =
      (forget U hU W q).app K ≫ (ambientIso U hU K c hK q).hom := by
  let := projection_isIso U hU W K c hK q
  let := inclusion_isIso U hU W K c hK q
  let := ambient_projection_isIso U hU K c hK q
  let := ambient_inclusion_isIso U hU K c hK q
  exact IntegralComparison.Functor.ConcentrationNaturality.square (functor U hU W q)
    (ambientFunctor U hU q) (forget U hU W q) K c

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.Concentration.Reference
