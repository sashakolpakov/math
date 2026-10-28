import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.RefinementChartRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.HomOpenCoverDetection

/-! # Family Hom Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.FamilyHomGluing.DirectedFamilyHomGluing

noncomputable section

/-! Descent of actual family morphisms on a locally directed open cover.
The local maps have their native pullback types; compatibility is equality
under the existing geometric base-change operation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} (C : S.OpenCover.{u})
  [Category C.I₀] [C.LocallyDirected] (X Y : Over S)

abbrev test (i : C.I₀) : Over S := Over.mk (C.f i)

abbrev testMap {i j : C.I₀} (f : i ⟶ j) : test C i ⟶ test C j :=
  Over.homMk (C.trans f) (C.trans_map f)

variable (p : ∀ i, (Over.pullback (C.f i)).obj X ⟶ (Over.pullback (C.f i)).obj Y)
  (hp : ∀ {i j : C.I₀} (f : i ⟶ j),
    Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange (testMap C f) (p j) = p i)

include hp in
private theorem total_natural {i j : C.I₀} (f : i ⟶ j) :
    (RefinementChartRecovery.parameterFamilyPullbackCover X C).trans f ≫ ((p j).left ≫ pullback.fst Y.hom (C.f j)) =
      (p i).left ≫ pullback.fst Y.hom (C.f i) := by
  have h := Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange_comp (testMap C f) (p j)
  rw [hp f] at h
  have hx : Single.ParameterBaseChange.singleParameterBaseChangeMap (testMap C f) X =
      (RefinementChartRecovery.parameterFamilyPullbackCover X C).trans f :=
    RefinementChartRecovery.singleParameterBaseChangeMap_eq_coverTransition X C f
  have hy : Single.ParameterBaseChange.singleParameterBaseChangeMap (testMap C f) Y ≫
      pullback.fst Y.hom (C.f j) = pullback.fst Y.hom (C.f i) :=
    Single.ParameterBaseChange.singleParameterBaseChangeMap_comp (testMap C f) Y
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ pullback.fst Y.hom (C.f j))
      ((congrArg (fun q => q ≫ (p j).left) hx).symm.trans h.symm)).trans
        ((Category.assoc _ _ _).trans (congrArg (fun q => (p i).left ≫ q) hy)))

omit [Category C.I₀] [Scheme.Cover.LocallyDirected C] in
private theorem total_over (i : C.I₀) :
    ((p i).left ≫ pullback.fst Y.hom (C.f i)) ≫ Y.hom =
      (RefinementChartRecovery.parameterFamilyPullbackCover X C).f i ≫ X.hom := by
  change ((p i).left ≫ pullback.fst Y.hom (C.f i)) ≫ Y.hom =
    pullback.fst X.hom (C.f i) ≫ X.hom
  have hw : (p i).left ≫ pullback.snd Y.hom (C.f i) = pullback.snd X.hom (C.f i) := (p i).w
  rw [Category.assoc, pullback.condition, ← Category.assoc, hw,
    ← pullback.condition]

def glue : X ⟶ Y :=
  (RefinementChartRecovery.parameterFamilyPullbackCover X C).glueMorphismsOverOfLocallyDirected
    (fun i => (p i).left ≫ pullback.fst Y.hom (C.f i))
    (total_natural C X Y p hp) (total_over C X Y p)

theorem glue_total (i : C.I₀) :
    pullback.fst X.hom (C.f i) ≫ (glue C X Y p hp).left =
      (p i).left ≫ pullback.fst Y.hom (C.f i) :=
  (RefinementChartRecovery.parameterFamilyPullbackCover X C).map_glueMorphismsOverOfLocallyDirected_left
    (fun i => (p i).left ≫ pullback.fst Y.hom (C.f i))
    (total_natural C X Y p hp) (total_over C X Y p) i

theorem glue_pullback (i : C.I₀) :
    (Over.pullback (C.f i)).map (glue C X Y p hp) = p i := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (Pullback.Comparisons.overPullback_map_left_fst (glue C X Y p hp) (C.f i)).trans
      (glue_total C X Y p hp i)
  · exact ((Over.pullback (C.f i)).map (glue C X Y p hp)).w.trans (p i).w.symm

theorem glue_unique (q : X ⟶ Y)
    (hq : ∀ i, (Over.pullback (C.f i)).map q = p i) : q = glue C X Y p hp :=
  HilbertConstruction.Over.HomOpenCoverDetection.overHom_eq_of_openCoverPullbacks C q (glue C X Y p hp)
    (fun i => (hq i).trans (glue_pullback C X Y p hp i).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.FamilyHomGluing.DirectedFamilyHomGluing
