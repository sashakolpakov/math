import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechHomotopyEquivalence
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.ConcentrationSingle

/-! # Concentration -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.Concentration

noncomputable section

/-! Canonical concentration on the original augmented support Čech
total, normalized against the actual cochain residue to a single. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechHomotopyEquivalence
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {R : Type u} [CommRing R] {ι : Type u} [LinearOrder ι] (U : ι → C)
  (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ)
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)

include hK in
theorem projection_isIso (q : ℕ) : IsIso ((Supported.CechHomotopyEquivalence.functor U q).map (CohomologyConcentration.projection K c)) := by
  let : QuasiIso (CohomologyConcentration.projection K c) := CohomologyConcentration.projection_quasiIso K c hK
  let : QuasiIso (AugmentedOrdered.CechForgetNaturality.map U (CohomologyConcentration.projection K c)) :=
    AugmentedOrdered.CechQuasiIso.quasiIso U R _
  change IsIso (homologyMap (AugmentedOrdered.CechForgetNaturality.map U (CohomologyConcentration.projection K c)) q)
  infer_instance

include hK in
theorem inclusion_isIso (q : ℕ) : IsIso ((Supported.CechHomotopyEquivalence.functor U q).map (CohomologyConcentration.inclusion K c)) := by
  let : QuasiIso (CohomologyConcentration.inclusion K c) := CohomologyConcentration.inclusion_quasiIso K c hK
  let : QuasiIso (AugmentedOrdered.CechForgetNaturality.map U (CohomologyConcentration.inclusion K c)) :=
    AugmentedOrdered.CechQuasiIso.quasiIso U R _
  change IsIso (homologyMap (AugmentedOrdered.CechForgetNaturality.map U (CohomologyConcentration.inclusion K c)) q)
  infer_instance

def iso (q : ℕ) : (Supported.CechHomotopyEquivalence.functor U q).obj K ≅
    (Supported.CechHomotopyEquivalence.functor U q).obj ((single (Cᵒᵖ ⥤ ModuleCat R) (.up ℕ) c).obj (K.homology c)) := by
  letI := projection_isIso U K c hK q
  letI := inclusion_isIso U K c hK q
  exact Functor.ConcentrationSingle.iso (Supported.CechHomotopyEquivalence.functor U q) K c

variable (N : Cᵒᵖ ⥤ ModuleCat.{u} R)
  (a : K ⟶ (single (Cᵒᵖ ⥤ ModuleCat R) (.up ℕ) c).obj N)

theorem map_to_single (q : ℕ) : (Supported.CechHomotopyEquivalence.functor U q).map a = (iso U K c hK q).hom ≫
    (Supported.CechHomotopyEquivalence.functor U q).map ((single (Cᵒᵖ ⥤ ModuleCat R) (.up ℕ) c).map
      (homologyMap a c ≫ (singleObjHomologySelfIso (.up ℕ) c N).hom)) := by
  let := projection_isIso U K c hK q
  let := inclusion_isIso U K c hK q
  let := projection_isIso U ((single _ (.up ℕ) c).obj N) c
    (fun n hn => exactAt_single_obj (.up ℕ) c N n hn) q
  exact Functor.ConcentrationSingle.map_to_single (Supported.CechHomotopyEquivalence.functor U q) K c N a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.Concentration
