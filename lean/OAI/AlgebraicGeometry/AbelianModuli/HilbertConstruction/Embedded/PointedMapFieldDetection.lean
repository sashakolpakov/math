import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.PointedMapFieldDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StalkPullbackDetection

/-! # Pointed Map Field Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.PointedMapFieldDetection

noncomputable section

/-! All field-valued base changes detect pointed morphisms of abelian schemes over a locally noetherian base when their product admits a relative projective embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem embeddedPointedMap_eq_of_fieldPullbacks
    {S : Scheme.{u}} [IsLocallyNoetherian S] {g h n : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n)
    [IsClosedImmersion j.left] (f q : A.scheme ⟶ B.scheme)
    (hf : η[A.scheme] ≫ f = η[B.scheme]) (hq : η[A.scheme] ≫ q = η[B.scheme])
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
  have hfp : η[(A.pullback b).scheme] ≫ (Over.pullback b).map f = η[(B.pullback b).scheme] :=
    (MappedMonoidHomEquations.mappedMonoidHom_one_iff (Over.pullback b) f).mpr (congrArg (Over.pullback b).map hf)
  have hqp : η[(A.pullback b).scheme] ≫ (Over.pullback b).map q = η[(B.pullback b).scheme] :=
    (MappedMonoidHomEquations.mappedMonoidHom_one_iff (Over.pullback b) q).mpr (congrArg (Over.pullback b).map hq)
  refine @Local.PointedMapFieldDetection.localPointedMap_eq_of_fieldPullbacks (S.presheaf.stalk x) _ hR _ _ _ _
    (A.pullback b) (B.pullback b) (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding b j) hj
    ((Over.pullback b).map f) ((Over.pullback b).map q) hfp hqp ?_
  intro K _ s
  exact (Iterated.PullbackMapEquality.overPullback_map_eq_iff_iterated s b f q).mp (h K (s ≫ b))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.PointedMapFieldDetection
