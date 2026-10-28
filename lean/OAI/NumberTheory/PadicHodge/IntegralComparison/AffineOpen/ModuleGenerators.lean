import Mathlib

/-! # Module Generators -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.ModuleGenerators

noncomputable section

/-!
# IntegralComparison: affine-coordinate generators give generators on the original open subscheme
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (hU : IsAffineOpen U)

def iso : (M.restrict hU.fromSpec).restrict hU.isoSpec.hom ≅ M.restrict U.ι :=
  ((Scheme.Modules.restrictFunctorComp hU.isoSpec.hom hU.fromSpec).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr hU.isoSpec_hom_fromSpec).app M

include hU in
theorem quasicoherent [(M.restrict hU.fromSpec).IsQuasicoherent] : (M.restrict U.ι).IsQuasicoherent := by
  let : ((M.restrict hU.fromSpec).restrict hU.isoSpec.hom).IsQuasicoherent :=
    inferInstance
  exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso (iso M U hU) inferInstance

def generatingSections (G : (M.restrict hU.fromSpec).GeneratingSections) :
    (M.restrict U.ι).GeneratingSections := by
  let hPres : Limits.PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor hU.isoSpec.hom) :=
    (Scheme.Modules.restrictAdjunction hU.isoSpec.hom).leftAdjoint_preservesColimits
  let G' := @SheafOfModules.GeneratingSections.map
    _ _ _ _ _ _ _ _ _ _ _ _ _ G (Scheme.Modules.restrictFunctor hU.isoSpec.hom) hPres
      (Scheme.Modules.restrictUnitIso hU.isoSpec.hom).symm
  exact (SheafOfModules.GeneratingSections.equivOfIso (iso M U hU))
    G'

theorem generatingSections_finite (G : (M.restrict hU.fromSpec).GeneratingSections) [hG : G.IsFiniteType] :
    (generatingSections M U hU G).IsFiniteType := by
  constructor
  change Finite G.I
  exact hG.finite

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.ModuleGenerators
