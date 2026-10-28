import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.TwistKernel
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.RestrictionTopValues
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-! # Closed Twist Kernel -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ClosedTwistKernel

noncomputable section

/-! The kernel of the twisted structure-sheaf restriction is measured
on each affine chart by the actual ideal of the scheme morphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

namespace PolarizationEmbedding

universe u
local instance c44ClosedTwistKernelMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules := SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

theorem twistedStructureMap_zero_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Y.Modules) (U : Y.Opens)
    (e : L.restrict U.ι ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) (x : Γ(L.restrict U.ι, ⊤)) :
    ((Scheme.Modules.restrictFunctor U.ι).map
      ((tensorRight L).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))).app ⊤
        (((Scheme.Modules.restrictFunctor U.ι).map (Open.TwistKernel.PolarizationEmbedding.unitTensorLineIso L).inv).app ⊤ x) = 0 ↔
      f.app U (U.topIso.hom (e.hom.app ⊤ x)) = 0 :=
  (Open.TwistKernel.PolarizationEmbedding.openTwist_restriction_zero_iff L U e
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) x).trans
      (RestrictionTopValues.PolarizationEmbedding.restrictSection_top_zero_iff U
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) (e.hom.app ⊤ x))

theorem twistedStructureMap_zero_iff_mem_ideal {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (L : Y.Modules) (U : Y.affineOpens)
    (e : L.restrict U.1.ι ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.1.toScheme) (x : Γ(L.restrict U.1.ι, ⊤)) :
    ((Scheme.Modules.restrictFunctor U.1.ι).map
      ((tensorRight L).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))).app ⊤
        (((Scheme.Modules.restrictFunctor U.1.ι).map (Open.TwistKernel.PolarizationEmbedding.unitTensorLineIso L).inv).app ⊤ x) = 0 ↔
      U.1.topIso.hom (e.hom.app ⊤ x) ∈ f.ker.ideal U := by
  rw [Scheme.Hom.ker_apply]
  exact twistedStructureMap_zero_iff f L U.1 e x

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ClosedTwistKernel
