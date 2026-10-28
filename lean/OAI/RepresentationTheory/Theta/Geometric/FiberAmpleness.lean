import OAI.RepresentationTheory.Theta.Geometric.AmpleAffinePullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace

/-! # Fiber Ampleness -/

namespace OAI.RepresentationTheory.Theta.Geometric.FiberAmpleness

noncomputable section

/-! An ample algebraic line bundle stays ample on every geometric fiber
of a proper complex scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace

theorem ample_pullback_proper_baseChange {X S T : Scheme} (p : X ⟶ S) [IsProper p]
    [CompactSpace T] (z : T ⟶ S) [IsAffineHom z] (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : L.IsAmple) :
    (L.pullback (pullback.fst p z)).IsAmple := by
  let : CompactSpace (pullback p z : Scheme) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd p z)
  let : IsAffineHom (pullback.fst p z) := isAffineHom_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback p z).flip ‹IsAffineHom z›
  exact AmpleAffinePullback.ample_pullback_of_affine (pullback.fst p z) L hL

theorem ample_on_geometric_fiber {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) (hL : L.IsAmple)
    (K : Type) [Field K] (z : Spec (.of K) ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) :
    (L.pullback (pullback.fst A.scheme.hom z)).IsAmple :=
  ample_pullback_proper_baseChange A.scheme.hom z L hL

end

end OAI.RepresentationTheory.Theta.Geometric.FiberAmpleness
