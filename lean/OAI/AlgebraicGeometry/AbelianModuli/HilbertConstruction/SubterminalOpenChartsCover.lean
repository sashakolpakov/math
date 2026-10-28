import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubterminalOpenChartRepresentation
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Subterminal Open Charts Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubterminalOpenChartsCover

noncomputable section

/-! Representations on an open cover of the base jointly cover a subterminal presheaf. The witnessing local lifts are defined on the actual pulled-back open cover of each test. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem restrictedRepresentedCharts_locallySurjective
    {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)
    (hs : ∀ T : Over S, Subsingleton (F.obj (.op T)))
    {ι : Type u} (U : ι → Scheme.{u}) (i : ∀ a, U a ⟶ S)
    (hi : ∀ a, IsOpenImmersion (i a))
    (hc : ∀ x : S, ∃ a y, i a y = x)
    (M : ∀ a, Over (U a)) (e : ∀ a, (Over.map (i a)).op ⋙ F ≅ yoneda.obj (M a)) :
    Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S)
      (Sigma.desc (fun a => SubterminalOpenChartRepresentation.restrictedRepresentedChartMap F (i a) (M a) (e a))) := by
  constructor
  intro T s
  let C : Scheme.OpenCover S := by
    have (a : ι) : IsOpenImmersion (i a) := hi a
    exact Scheme.Cover.mkOfCovers ι U i hc
  let V := fun a => SubterminalRelativeChart.baseChartTest (i a) T
  let r := fun a => SubterminalRelativeChart.baseChartProjection (i a) T
  have hcover : Sieve.ofArrows V r ∈ (Scheme.zariskiTopology.over S) T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact Scheme.Cover.mem_grothendieckTopology (C.pullback₁ T.hom)
  apply (Scheme.zariskiTopology.over S).superset_covering _ hcover
  apply (Sieve.generate_le_iff _ _).mpr
  rintro W f ⟨a⟩
  let m := SubterminalOpenChartRepresentation.restrictedRepresentedChartPullbackArrow F (i a) (M a) (e a) T (yonedaEquiv.symm s)
  refine ⟨(Sigma.ι (fun a => yoneda.obj ((Over.map (i a)).obj (M a))) a).app (.op (V a)) m, ?_⟩
  exact @Subsingleton.elim _ (hs (V a)) _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubterminalOpenChartsCover
