import OAI.AlgebraicGeometry.Resolution.Blowups.ReducedCenterPointedDescent
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.PullbackCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterComponents

/-! # Center Open Overlap -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterOpenOverlap.Construction

noncomputable section

/-! Smooth center ideals agree on actual open overlaps when their point supports agree there. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem smooth_center_open_overlap_eq
    {X U V : Scheme} (j : U ⟶ X) (l : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion l]
    (f : U ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (g : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I : U.IdealSheafData) (J : V.IdealSheafData)
    [Smooth (I.subschemeι ≫ f)] [Smooth (J.subschemeι ≫ g)]
    (h : ∀ (x : U) (y : V), j x = l y → (x ∈ I.support ↔ y ∈ J.support)) :
    I.comap (pullback.fst j l) = J.comap (pullback.snd j l) := by
  let : Smooth ((I.comap (pullback.fst j l)).subschemeι ≫ (pullback.fst j l ≫ f)) :=
    Etale.PullbackCenter.Construction.idealSheaf_comap_etale_smooth_center f (pullback.fst j l) I
  let : Smooth ((J.comap (pullback.snd j l)).subschemeι ≫ (pullback.snd j l ≫ g)) :=
    Etale.PullbackCenter.Construction.idealSheaf_comap_etale_smooth_center g (pullback.snd j l) J
  let : IsReduced (I.comap (pullback.fst j l)).subscheme :=
    CenterComponents.Construction.smooth_complex_scheme_isReduced ((I.comap (pullback.fst j l)).subschemeι ≫ (pullback.fst j l ≫ f))
  let : IsReduced (J.comap (pullback.snd j l)).subscheme :=
    CenterComponents.Construction.smooth_complex_scheme_isReduced ((J.comap (pullback.snd j l)).subschemeι ≫ (pullback.snd j l ≫ g))
  apply ReducedCenterPointedDescent.Construction.idealSheaf_eq_of_reduced_support_eq
  rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap]
  ext x
  exact h _ _ (congrArg (fun q : pullback j l ⟶ X => q x) (pullback.condition (f := j) (g := l)))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterOpenOverlap.Construction
