import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.HomFieldDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StalkPullbackDetection

/-! # Hom Field Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.HomFieldDetection

noncomputable section

/-! All field-valued base changes detect native homomorphisms of abelian schemes over a locally noetherian base when their product admits a relative projective embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.Obj

universe u

theorem embeddedAbelianHom_eq_of_fieldPullbacks
    {S : Scheme.{u}} [IsLocallyNoetherian S] {g h n : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n)
    [IsClosedImmersion j.left] (f q : A.scheme ⟶ B.scheme) [IsMonHom f] [IsMonHom q]
    (h : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ S),
      (Over.pullback s).map f = (Over.pullback s).map q) : f = q := by
  have : IsLocallyNoetherian A.scheme.left := LocallyOfFiniteType.isLocallyNoetherian A.scheme.hom
  apply StalkPullbackDetection.overHom_eq_of_stalkPullbacks
  intro x
  have hR : IsNoetherianRing (S.presheaf.stalk x) :=
    AlgebraicGeometry.instIsNoetherianRingCarrierStalkCommRingCatPresheafOfIsLocallyNoetherian
      (X := S) (x := x)
  let b := S.fromSpecStalk x
  have hj : IsClosedImmersion (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding b j).left :=
    RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding_closed b j
  have hf : IsMonHom ((Over.pullback b).map f) :=
    inferInstance
  have hq : IsMonHom ((Over.pullback b).map q) :=
    inferInstance
  refine @Local.HomFieldDetection.localAbelianHom_eq_of_fieldPullbacks (S.presheaf.stalk x) _ hR _ _ _ _
    (A.pullback b) (B.pullback b) (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding b j) hj
    ((Over.pullback b).map f) ((Over.pullback b).map q) hf hq ?_
  intro K _ s
  exact (Iterated.PullbackMapEquality.overPullback_map_eq_iff_iterated s b f q).mp (h K (s ≫ b))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.HomFieldDetection
