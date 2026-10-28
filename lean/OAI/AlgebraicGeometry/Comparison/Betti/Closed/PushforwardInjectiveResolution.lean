import OAI.AlgebraicGeometry.Comparison.Betti.Closed.AdditivePushforward
import OAI.AlgebraicGeometry.Comparison.Betti.PushforwardInjectiveResolution

/-! # Pushforward Injective Resolution -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Closed.PushforwardInjectiveResolution.Cech

noncomputable section

/-! The original direct image of an injective resolution remains an injective resolution along a closed embedding. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : Topology.IsInducing f)
  (hclosed : IsClosed (Set.range f)) (F : TopCat.Sheaf AddCommGrpCat.{0} X)

include hf hclosed

theorem closedPushedInjectiveCocomplex_exact_succ (n : ℕ) :
    (PushforwardResolutionExact.Cech.pushedInjectiveCocomplex f F).ExactAt (n + 1) := by
  let I : InjectiveResolution F := injectiveResolution (SheafCohomology.Cech.Compat.TopCat.Sheaf.toSiteSheaf F)
  let S := ShortComplex.mk (I.cocomplex.d n (n + 1)) (I.cocomplex.d (n + 1) (n + 2))
    (I.cocomplex.d_comp_d n (n + 1) (n + 2))
  have hs : (S.map (TopCat.Sheaf.pushforward AddCommGrpCat f)).Exact :=
    AdditivePushforward.Cech.closedAdditivePushforward_map_exact f hf hclosed S (I.exact_succ n)
  exact ((PushforwardResolutionExact.Cech.pushedInjectiveCocomplex f F).exactAt_iff' n (n + 1) (n + 2)
    (by simp) (by simp)).mpr hs

def closedPushedInjectiveResolution :
    InjectiveResolution ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) where
  cocomplex := PushforwardResolutionExact.Cech.pushedInjectiveCocomplex f F
  injective n := by
    let I : InjectiveResolution F := injectiveResolution (SheafCohomology.Cech.Compat.TopCat.Sheaf.toSiteSheaf F)
    exact (TopCat.Sheaf.pushforward AddCommGrpCat f).injective_obj_of_injective (I.injective n)
  ι := AugmentedComplexQuasiIso.Ext.nonnegativeAugmentation (C := TopCat.Sheaf AddCommGrpCat.{0} Y)
    (PushforwardResolutionExact.Cech.pushedInjectiveCocomplex f F) (PushforwardResolutionExact.Cech.pushedInjectiveAugmentation f F)
    (PushforwardResolutionExact.Cech.pushedInjectiveAugmentation_comp f F)
  quasiIso := AugmentedComplexQuasiIso.Ext.nonnegativeAugmentation_quasiIso _ _ _
    (PushforwardResolutionExact.Cech.pushedInjectiveAugmentation_exact f F)
    (closedPushedInjectiveCocomplex_exact_succ f hf hclosed F)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Closed.PushforwardInjectiveResolution.Cech
