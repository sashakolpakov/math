import OAI.AlgebraicGeometry.Comparison.Betti.PushforwardResolutionExact
import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.PushforwardInjective
import OAI.AlgebraicGeometry.Comparison.Betti.AugmentedComplexQuasiIso

/-! # Pushforward Injective Resolution -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PushforwardInjectiveResolution.Cech

noncomputable section

/-! An injective resolution after direct image under local cohomological vanishing. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
  (hlocal : ∀ (V : Opens Y) (y : V), ∃ W : Opens Y, W ≤ V ∧ y.val ∈ W ∧
    ∀ q, Subsingleton (Sheaf.H
      ((SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat ((Opens.map f).obj W).isOpenEmbedding).obj F) (q + 1)))

def pushedInjectiveResolution :
    InjectiveResolution ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) where
  cocomplex := PushforwardResolutionExact.Cech.pushedInjectiveCocomplex f F
  injective n := by
    let I : InjectiveResolution F := injectiveResolution (SheafCohomology.Cech.Compat.TopCat.Sheaf.toSiteSheaf F)
    exact (TopCat.Sheaf.pushforward AddCommGrpCat f).injective_obj_of_injective (I.injective n)
  ι := AugmentedComplexQuasiIso.Ext.nonnegativeAugmentation (C := TopCat.Sheaf AddCommGrpCat.{u} Y)
    (PushforwardResolutionExact.Cech.pushedInjectiveCocomplex f F)
    (PushforwardResolutionExact.Cech.pushedInjectiveAugmentation f F) (PushforwardResolutionExact.Cech.pushedInjectiveAugmentation_comp f F)
  quasiIso := AugmentedComplexQuasiIso.Ext.nonnegativeAugmentation_quasiIso _ _ _
    (PushforwardResolutionExact.Cech.pushedInjectiveAugmentation_exact f F) (fun n => by
      exact (PushforwardResolutionExact.Cech.pushedInjectiveCocomplex f F).exactAt_iff' n (n + 1) (n + 2)
        (by simp) (by simp) |>.mpr (PushforwardResolutionExact.Cech.pushedInjectiveCocomplex_exact_succ f F hlocal n))

end

end OAI.AlgebraicGeometry.Comparison.Betti.PushforwardInjectiveResolution.Cech
