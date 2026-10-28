import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.DimensionBound
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechHomotopyEquiv

/-! # Pushforward -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.Pushforward.Comparison

noncomputable section

/-! The native module-valued Čech cohomology on an inverse-image
cover agrees with the ordered base-linear Čech cohomology of the
actual pushforward. The comparison retains every original sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  (M : X.left.Modules) {ι : Type u} (U : ι → Y.left.Opens)

local instance opens_finiteLimits : PreservesFiniteLimits (Opens.map f.left.base) := by
  change PreservesFiniteLimits (OrderHom.ofClass f.left.base.frameHom).toFunctor
  infer_instance

def complexIso :
    ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj
        (DimensionBound.complex R X M (fun i => f.left ⁻¹ᵁ U i)) ≅
      ((AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of R))).mapHomologicalComplex (.up ℕ)).obj
        (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex Y.hom ((Scheme.Modules.pushforward f.left).obj M) U) :=
  DimensionBound.forgetIso R X M (fun i => f.left ⁻¹ᵁ U i) ≪≫
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (Opens.map f.left.base) U M.presheaf).symm ≪≫
      (AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseCechComplexForgetIso Y.hom ((Scheme.Modules.pushforward f.left).obj M) U).symm

variable [LinearOrder ι]

def cohomologyIso (n : ℕ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
        ((DimensionBound.complex R X M (fun i => f.left ⁻¹ᵁ U i)).homology n) ≅
      (AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of R))).obj
        ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex Y.hom
          ((Scheme.Modules.pushforward f.left).obj M) U).homology n) :=
  (((DimensionBound.complex R X M (fun i => f.left ⁻¹ᵁ U i)).sc n).mapHomologyIso
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).symm ≪≫
    HomologicalComplex.homologyMapIso (complexIso R X Y f M U) n ≪≫
      ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex Y.hom ((Scheme.Modules.pushforward f.left).obj M) U).sc n).mapHomologyIso
        (AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of R))) ≪≫
          (AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of R))).mapIso
            (AlgebraicGeometry.SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomologyIso Y.hom ((Scheme.Modules.pushforward f.left).obj M) U n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.Pushforward.Comparison
