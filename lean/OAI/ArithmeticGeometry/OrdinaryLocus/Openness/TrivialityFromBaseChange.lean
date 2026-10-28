import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiberTrivialityBaseChange
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ResidueFieldPointLift

/-! # Triviality From Base Change -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TrivialityFromBaseChange.Construction

noncomputable section

/-! A trivialization after a base immersion gives the ordinary residue-field fiber trivialization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

def lineBundleFiberTrivialization_of_baseChange
    {X S T : Scheme.{u}} (π : X ⟶ S) (g : T ⟶ S) [SurjectiveOnStalks g]
    (L : X.Modules) (t : T)
    (e : (Scheme.Modules.pullback (pullback.fst π g)).obj L ≅ LineBundle.Construction.structureSheafModule (pullback π g)) :
    (Scheme.Modules.pullback (π.fiberι (g t))).obj L ≅ LineBundle.Construction.structureSheafModule (π.fiber (g t)) := by
  let r := ResidueFieldPointLift.Construction.residueFieldPointLift g t
  let h : π.fiber (g t) ⟶ pullback π g :=
    pullback.lift (π.fiberι (g t)) (π.fiberToSpecResidueField (g t) ≫ r) (by
      rw [π.fiber_fac, Category.assoc, ResidueFieldPointLift.Construction.residueFieldPointLift_comp])
  have hh : h ≫ pullback.fst π g = π.fiberι (g t) := pullback.lift_fst _ _ _
  exact (Scheme.Modules.pullbackCongr hh.symm).app L ≪≫
    FiberTrivialityBaseChange.Construction.pullbackTrivialization_comp (pullback.fst π g) h L e

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TrivialityFromBaseChange.Construction
