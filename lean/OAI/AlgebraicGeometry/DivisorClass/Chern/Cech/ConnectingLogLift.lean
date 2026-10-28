import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingResolutionCocycle
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.DegreeOneBoundary

/-! # Connecting Log Lift -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.ConnectingLogLift

noncomputable section

/-! A lifted Cech logarithm gives both native resolution equations through the actual short exact sequence. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)
  {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)} (hS : S.ShortExact)
  (R : InjectiveResolution S.X₁)
  (l : ((CategoryTheory.cechComplexFunctor U).obj S.X₂.obj).X 1)

def nativeConnectingLogLift : ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U R.cocomplex).X 0).X 1 :=
  ((CategoryTheory.cechComplexFunctor U).map (ConnectingResolutionCocycle.connectingResolutionMiddle hS R).hom).f 1 l

theorem nativeConnectingLogLift_delta
    (k : ((CategoryTheory.cechComplexFunctor U).obj S.X₁.obj).X 2)
    (hk : ((CategoryTheory.cechComplexFunctor U).map S.f.hom).f 2 k =
      ((CategoryTheory.cechComplexFunctor U).obj S.X₂.obj).d 1 2 l) :
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U R.cocomplex).X 0).d 1 2 (nativeConnectingLogLift U hS R l) =
      ((CategoryTheory.cechComplexFunctor U).map (R.ι.f 0).hom).f 2 k := by
  let B := (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).map (ConnectingResolutionCocycle.connectingResolutionMiddle hS R)
  have hd := ConcreteCategory.congr_hom (B.comm 1 2) l
  change ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U R.cocomplex).X 0).d 1 2 (nativeConnectingLogLift U hS R l) =
    B.f 2 (((CategoryTheory.cechComplexFunctor U).obj S.X₂.obj).d 1 2 l) at hd
  have hm : (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).map S.f ≫ B =
      (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).map (show S.X₁ ⟶ R.cocomplex.X 0 from R.ι.f 0) := by
    change (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).map S.f ≫
      (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).map (ConnectingResolutionCocycle.connectingResolutionMiddle hS R) = _
    rw [← Functor.map_comp, ConnectingResolutionCocycle.connectingResolutionMiddle_comm]
  have hv := ConcreteCategory.congr_hom (congrArg (fun g => g.f 2) hm) k
  exact hd.trans ((congrArg (B.f 2) hk.symm).trans hv)

theorem nativeConnectingLogLift_d
    (k : ((CategoryTheory.cechComplexFunctor U).obj S.X₃.obj).X 1)
    (hk : ((CategoryTheory.cechComplexFunctor U).map S.g.hom).f 1 l = k) :
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U R.cocomplex).d 0 1).f 1 (nativeConnectingLogLift U hS R l) =
      ((CategoryTheory.cechComplexFunctor U).map (ConnectingResolutionCocycle.connectingResolutionQuotient hS R).hom).f 1 k := by
  have hm : (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).map S.g ≫
      (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).map (ConnectingResolutionCocycle.connectingResolutionQuotient hS R) =
      (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).map (ConnectingResolutionCocycle.connectingResolutionMiddle hS R) ≫
        (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).map (R.cocomplex.d 0 1) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ConnectingResolutionCocycle.connectingResolutionQuotient_comm]
  have hv := ConcreteCategory.congr_hom (congrArg (fun g => g.f 1) hm) l
  refine hv.symm.trans ?_
  exact congrArg (((CategoryTheory.cechComplexFunctor U).map
    (ConnectingResolutionCocycle.connectingResolutionQuotient hS R).hom).f 1) hk

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.ConnectingLogLift
