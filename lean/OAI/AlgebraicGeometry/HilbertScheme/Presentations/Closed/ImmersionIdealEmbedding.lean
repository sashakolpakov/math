import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Immersion Ideal Embedding -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ImmersionIdealEmbedding

noncomputable section

/-! Closed subschemes of a closed ambient subscheme correspond exactly
to ambient ideals containing its defining ideal. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsClosedImmersion j]

theorem ideal_comap_map_closed (I : X.IdealSheafData) : (I.map j).comap j = I := by
  have h : IsPullback I.subschemeι (𝟙 I.subscheme) j (I.subschemeι ≫ j) :=
    IsPullback.of_vert_isIso_mono ⟨(Category.id_comp _).symm⟩
  change (I.subschemeι ≫ j).ker.comap j = I
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso h.isoPullback.hom,
    h.isoPullback_hom_fst, Scheme.IdealSheafData.ker_subschemeι]

theorem ideal_map_closed_injective : Function.Injective (fun I : X.IdealSheafData => I.map j) := by
  intro I J h
  have he := congrArg (fun K : Y.IdealSheafData => K.comap j) h
  simpa only [ideal_comap_map_closed] using he

theorem ideal_map_comap_closed (J : Y.IdealSheafData) (hJ : j.ker ≤ J) :
    (J.comap j).map j = J := by
  let l := IsClosedImmersion.lift j J.subschemeι (by simpa only [J.ker_subschemeι] using hJ)
  have hl : l ≫ j = J.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have hk : l.ker.map j = J := by
    rw [Scheme.IdealSheafData.map_ker, hl, J.ker_subschemeι]
  rw [← hk, ideal_comap_map_closed]

theorem ideal_map_closed_range (J : Y.IdealSheafData) :
    (∃ I : X.IdealSheafData, I.map j = J) ↔ j.ker ≤ J := by
  constructor
  · rintro ⟨I, rfl⟩
    exact Scheme.Hom.le_ker_comp I.subschemeι j
  · intro hJ
    exact ⟨J.comap j, ideal_map_comap_closed j J hJ⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ImmersionIdealEmbedding
