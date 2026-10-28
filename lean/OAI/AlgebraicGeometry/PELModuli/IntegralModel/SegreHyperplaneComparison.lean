import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SegreTensorFrames
import OAI.RepresentationTheory.Theta.Geometric.EqualFrameTransitionGluing

/-! # Segre Hyperplane Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SegreHyperplaneComparison

noncomputable section

/-! The exact Segre chart equations of Presentations identify the actual hyperplane
pullback with the O(1,1) tensor sheaf, by gluing native frame isomorphisms. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace PolarizationEmbedding

variable {S : Scheme.{0}} {X Y : Over S}
  (BX : HilbertScheme.Presentations.Has.Core.ProjectivePresentation X) (BY : HilbertScheme.Presentations.Has.Core.ProjectivePresentation Y)
  (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (X ⨯ Y))
  (c : Fin (B.dimension + 1) ≃ Fin (BX.dimension + 1) × Fin (BY.dimension + 1))
  (hU : ∀ q, SegreTensorFrames.PolarizationEmbedding.segreChartOpen BX BY q = B.coordinateOpen (c.symm q))
  (hR : ∀ q r,
    (X ⨯ Y).left.presheaf.map (homOfLE (hU q).le).op
        (B.coordinateRatio (c.symm q) (c.symm r)) =
      (prod.fst : X ⨯ Y ⟶ X).left.appLE (BX.coordinateOpen q.1) (SegreTensorFrames.PolarizationEmbedding.segreChartOpen BX BY q)
        inf_le_left (BX.coordinateRatio q.1 r.1) *
      (prod.snd : X ⨯ Y ⟶ Y).left.appLE (BY.coordinateOpen q.2) (SegreTensorFrames.PolarizationEmbedding.segreChartOpen BX BY q)
        inf_le_right (BY.coordinateRatio q.2 r.2))

include hR in
theorem segre_coordinateRatio_restrict
    (q r : Fin (BX.dimension + 1) × Fin (BY.dimension + 1))
    (U : (X ⨯ Y).left.Opens) (h : U ≤ SegreTensorFrames.PolarizationEmbedding.segreChartOpen BX BY q) :
    (X ⨯ Y).left.presheaf.map (homOfLE (h.trans (hU q).le)).op
        (B.coordinateRatio (c.symm q) (c.symm r)) =
      (prod.fst : X ⨯ Y ⟶ X).left.appLE (BX.coordinateOpen q.1) U
        (h.trans inf_le_left) (BX.coordinateRatio q.1 r.1) *
      (prod.snd : X ⨯ Y ⟶ Y).left.appLE (BY.coordinateOpen q.2) U
        (h.trans inf_le_right) (BY.coordinateRatio q.2 r.2) := by
  have he := congrArg ((X ⨯ Y).left.presheaf.map (homOfLE h).op) (hR q r)
  rw [map_mul] at he
  have hl := ConcreteCategory.congr_hom
    ((prod.fst : X ⨯ Y ⟶ X).left.appLE_map inf_le_left (homOfLE h).op)
      (BX.coordinateRatio q.1 r.1)
  have hr := ConcreteCategory.congr_hom
    ((prod.snd : X ⨯ Y ⟶ Y).left.appLE_map inf_le_right (homOfLE h).op)
      (BY.coordinateRatio q.2 r.2)
  change (X ⨯ Y).left.presheaf.map (homOfLE h).op
      ((prod.fst : X ⨯ Y ⟶ X).left.appLE (BX.coordinateOpen q.1)
        (SegreTensorFrames.PolarizationEmbedding.segreChartOpen BX BY q) inf_le_left (BX.coordinateRatio q.1 r.1)) = _ at hl
  change (X ⨯ Y).left.presheaf.map (homOfLE h).op
      ((prod.snd : X ⨯ Y ⟶ Y).left.appLE (BY.coordinateOpen q.2)
        (SegreTensorFrames.PolarizationEmbedding.segreChartOpen BX BY q) inf_le_right (BY.coordinateRatio q.2 r.2)) = _ at hr
  rw [hl, hr] at he
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp] at he
  exact he

def segrePresentationFrame (j : Fin (B.dimension + 1))
    (q : Fin (BX.dimension + 1) × Fin (BY.dimension + 1)) :
    (Presentations.PresentationFrames.PolarizationEmbedding.e34HyperplanePullback B j).restrict (SegreTensorFrames.PolarizationEmbedding.segreChartOpen BX BY q).ι ≅
      SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (SegreTensorFrames.PolarizationEmbedding.segreChartOpen BX BY q).toScheme :=
  SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (hU q).le (Presentations.PresentationFrames.PolarizationEmbedding.e34HyperplaneFrame B j (c.symm q))

theorem segrePresentationFrame_restrict (j : Fin (B.dimension + 1))
    (q : Fin (BX.dimension + 1) × Fin (BY.dimension + 1))
    (U : (X ⨯ Y).left.Opens) (h : U ≤ SegreTensorFrames.PolarizationEmbedding.segreChartOpen BX BY q) :
    SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h (segrePresentationFrame BX BY B c hU j q) =
      SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (h.trans (hU q).le)
        (Presentations.PresentationFrames.PolarizationEmbedding.e34HyperplaneFrame B j (c.symm q)) :=
  SheafCohomology.Projective.OpenFrameTransitivity.Scheme.Modules.restrictOpenTrivialization_comp (hU q).le h _

def segreRatioProduct
    (q r : Fin (BX.dimension + 1) × Fin (BY.dimension + 1))
    (U : (X ⨯ Y).left.Opens) (h : U ≤ SegreTensorFrames.PolarizationEmbedding.segreChartOpen BX BY q) : Γ((X ⨯ Y).left, U) :=
  (prod.fst : X ⨯ Y ⟶ X).left.appLE (BX.coordinateOpen q.1) U
    (h.trans inf_le_left) (BX.coordinateRatio q.1 r.1) *
  (prod.snd : X ⨯ Y ⟶ Y).left.appLE (BY.coordinateOpen q.2) U
    (h.trans inf_le_right) (BY.coordinateRatio q.2 r.2)

def segreOverlapRatio (q r : Fin (BX.dimension + 1) × Fin (BY.dimension + 1)) :
    Γ((X ⨯ Y).left, SegreTensorFrames.PolarizationEmbedding.segreChartOpen BX BY q ⊓ SegreTensorFrames.PolarizationEmbedding.segreChartOpen BX BY r) :=
  segreRatioProduct BX BY q r _ inf_le_left

include hR in
theorem segrePresentationFrame_transition_on (j : Fin (B.dimension + 1))
    (q r : Fin (BX.dimension + 1) × Fin (BY.dimension + 1))
    (U : (X ⨯ Y).left.Opens) (hq : U ≤ SegreTensorFrames.PolarizationEmbedding.segreChartOpen BX BY q) (hr : U ≤ SegreTensorFrames.PolarizationEmbedding.segreChartOpen BX BY r) :
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hq (segrePresentationFrame BX BY B c hU j q)).hom =
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hr (segrePresentationFrame BX BY B c hU j r)).hom ≫
        SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (U.topIso.inv (segreRatioProduct BX BY q r U hq)) := by
  have hl := congrArg Iso.hom (segrePresentationFrame_restrict BX BY B c hU j q U hq)
  have hh := congrArg Iso.hom (segrePresentationFrame_restrict BX BY B c hU j r U hr)
  have he := Presentations.PresentationFrames.PolarizationEmbedding.e34HyperplaneFrame_transition_on B j (c.symm q) (c.symm r) U
    (hq.trans (hU q).le) (hr.trans (hU r).le)
  have hs := segre_coordinateRatio_restrict BX BY B c hU hR q r U hq
  exact hl.trans (he.trans ((congrArg (fun a =>
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (hr.trans (hU r).le)
      (Presentations.PresentationFrames.PolarizationEmbedding.e34HyperplaneFrame B j (c.symm r))).hom ≫
        SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (U.topIso.inv a)) hs).trans
    (congrArg (fun f => f ≫ SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection
      (U.topIso.inv (segreRatioProduct BX BY q r U hq))) hh.symm)))

include hR in
theorem segrePresentationFrame_overlap (j : Fin (B.dimension + 1))
    (q r : Fin (BX.dimension + 1) × Fin (BY.dimension + 1)) :
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization inf_le_left
      (segrePresentationFrame BX BY B c hU j q)).hom =
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization inf_le_right
        (segrePresentationFrame BX BY B c hU j r)).hom ≫
        SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection
          ((SegreTensorFrames.PolarizationEmbedding.segreChartOpen BX BY q ⊓ SegreTensorFrames.PolarizationEmbedding.segreChartOpen BX BY r).topIso.inv (segreOverlapRatio BX BY q r)) :=
  segrePresentationFrame_transition_on BX BY B c hU hR j q r _ inf_le_left inf_le_right

theorem segreTensorFrame_overlap (i₀ : Fin (BX.dimension + 1)) (j₀ : Fin (BY.dimension + 1))
    (q r : Fin (BX.dimension + 1) × Fin (BY.dimension + 1)) :
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization inf_le_left (SegreTensorFrames.PolarizationEmbedding.segreTensorFrame BX BY i₀ j₀ q)).hom =
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization inf_le_right (SegreTensorFrames.PolarizationEmbedding.segreTensorFrame BX BY i₀ j₀ r)).hom ≫
        SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection
          ((SegreTensorFrames.PolarizationEmbedding.segreChartOpen BX BY q ⊓ SegreTensorFrames.PolarizationEmbedding.segreChartOpen BX BY r).topIso.inv (segreOverlapRatio BX BY q r)) :=
  SegreTensorFrames.PolarizationEmbedding.segreTensorFrame_transition_on BX BY i₀ j₀ q r _ inf_le_left inf_le_right

include hR in
theorem exists_segre_hyperplane_iso_of_charts
    (j : Fin (B.dimension + 1)) (i₀ : Fin (BX.dimension + 1)) (j₀ : Fin (BY.dimension + 1)) :
    Nonempty (Presentations.PresentationFrames.PolarizationEmbedding.e34HyperplanePullback B j ≅ SegreTensorFrames.PolarizationEmbedding.segreTensorHyperplane BX BY i₀ j₀) := by
  exact RepresentationTheory.Theta.Geometric.EqualFrameTransitionGluing.exists_iso_of_equal_frame_transitions
    (X := (X ⨯ Y).left) (ι := Fin (BX.dimension + 1) × Fin (BY.dimension + 1))
    (Presentations.PresentationFrames.PolarizationEmbedding.e34HyperplanePullback B j) (SegreTensorFrames.PolarizationEmbedding.segreTensorHyperplane BX BY i₀ j₀)
    (SegreTensorFrames.PolarizationEmbedding.segreChartOpen BX BY) (SegreTensorFrames.PolarizationEmbedding.segreChartOpens_cover BX BY)
    (fun q r => SegreTensorFrames.PolarizationEmbedding.segreChartOpen BX BY q ⊓ SegreTensorFrames.PolarizationEmbedding.segreChartOpen BX BY r)
    (fun _ _ => inf_le_left) (fun _ _ => inf_le_right) (fun _ _ => le_rfl)
    (segrePresentationFrame BX BY B c hU j) (SegreTensorFrames.PolarizationEmbedding.segreTensorFrame BX BY i₀ j₀)
    (segreOverlapRatio BX BY)
    (segrePresentationFrame_overlap BX BY B c hU hR j)
    (segreTensorFrame_overlap BX BY i₀ j₀)

theorem exists_segre_hyperplane_iso
    (hSegre : HilbertScheme.Presentations.Segre.Open.Core.IsSegrePresentation BX BY B)
    (j : Fin (B.dimension + 1)) (i₀ : Fin (BX.dimension + 1)) (j₀ : Fin (BY.dimension + 1)) :
    Nonempty (Presentations.PresentationFrames.PolarizationEmbedding.e34HyperplanePullback B j ≅ SegreTensorFrames.PolarizationEmbedding.segreTensorHyperplane BX BY i₀ j₀) := by
  classical
  obtain ⟨c, hc⟩ := hSegre
  choose hU hR using hc
  exact exists_segre_hyperplane_iso_of_charts BX BY B c
    (fun q => hU q.1 q.2) (fun q r => hR q.1 q.2 r.1 r.2) j i₀ j₀

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SegreHyperplaneComparison
