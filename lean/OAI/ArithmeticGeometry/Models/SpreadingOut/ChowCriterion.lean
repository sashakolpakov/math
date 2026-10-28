import OAI.ArithmeticGeometry.Models.SpreadingOut.ChowChart
import OAI.ArithmeticGeometry.Models.SpreadingOut.GraphClosure

/-! # Chow Criterion -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.ChowCriterion.Construction

noncomputable section

/-! The chart criterion that turns a proper rational graph closure into a
closed subscheme of the chosen proper ambient space. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem closed_graph_projection_of_chart_cover
    {S : Scheme.{u}} {W Z X P : Over S}
    [IsReduced Z.left] [IsProper Z.hom] [IsSeparated X.hom] [IsSeparated P.hom]
    (d : W ⟶ Z) [IsDominant d.left] (p : Z ⟶ X) (q : Z ⟶ P)
    [IsClosedImmersion (pullback.lift p.left q.left (p.w.trans q.w.symm))]
    {ι : Type*} (Q : ι → Over S) (hQ : ∀ i, IsSeparated (Q i).hom)
    (π : ∀ i, P ⟶ Q i) (V : ι → X.left.Opens) (hV : (⨆ i, V i) = ⊤)
    (A : ∀ i, (Q i).left.Opens)
    (k : ∀ i, W ⟶ OpenOver.Construction.overOpen X (V i))
    (e : ∀ i, OpenOver.Construction.overOpen X (V i) ⟶ OpenOver.Construction.overOpen (Q i) (A i))
    (he : ∀ i, IsClosedImmersion (e i).left)
    (hp : ∀ i, d ≫ p = k i ≫ OpenOver.Construction.overOpenInclusion X (V i))
    (hq : ∀ i, d ≫ q ≫ π i = k i ≫ e i ≫ OpenOver.Construction.overOpenInclusion (Q i) (A i)) :
    IsClosedImmersion q.left := by
  have : IsProper (q.left ≫ P.hom) := by rw [q.w]; infer_instance
  have : IsProper q.left := IsProper.of_comp q.left P.hom
  let B : ι → P.left.Opens := fun i ↦ (π i).left ⁻¹ᵁ A i
  apply ClosedProjection.Construction.proper_closedImmersion_of_target_charts q.left B
  · rintro _ ⟨z, rfl⟩
    have hz : p.left z ∈ (⨆ i, V i) := by rw [hV]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
    have := hQ i
    have hle := ChowChart.Construction.dense_chart_extension_preimage_le d p (q ≫ π i)
      (V i) (A i) (k i) (e i) (hp i) (hq i)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hle hi⟩
  · intro i
    have := he i
    exact ChowChart.Construction.dense_chart_closed_restriction d p q (π i) (V i) (A i) (k i) (e i) (hp i) (hq i)

/-- The graph closure of compatible affine-chart maps is closed in the
proper target. Together with its proper surjection to the source, this is
the geometric step in the projective-cover construction. -/
theorem graphClosureToP_closed_of_chart_cover
    {S : Scheme.{u}} {W X P : Over S}
    [IsReduced W.left] [IsProper X.hom] [IsProper P.hom]
    (j : W ⟶ X) [IsOpenImmersion j.left] (a : W ⟶ P)
    [QuasiCompact (GraphClosure.Construction.rationalGraph j a)]
    {ι : Type*} (Q : ι → Over S) (hQ : ∀ i, IsSeparated (Q i).hom)
    (π : ∀ i, P ⟶ Q i) (V : ι → X.left.Opens) (hV : (⨆ i, V i) = ⊤)
    (A : ∀ i, (Q i).left.Opens)
    (k : ∀ i, W ⟶ OpenOver.Construction.overOpen X (V i))
    (e : ∀ i, OpenOver.Construction.overOpen X (V i) ⟶ OpenOver.Construction.overOpen (Q i) (A i))
    (he : ∀ i, IsClosedImmersion (e i).left)
    (hj : ∀ i, j = k i ≫ OpenOver.Construction.overOpenInclusion X (V i))
    (ha : ∀ i, a ≫ π i = k i ≫ e i ≫ OpenOver.Construction.overOpenInclusion (Q i) (A i)) :
    IsClosedImmersion (GraphClosure.Construction.graphClosureToP j a).left := by
  let Z := GraphClosure.Construction.graphClosure j a
  let d := GraphClosure.Construction.graphClosureLift j a
  let p := GraphClosure.Construction.graphClosureToX j a
  let q := GraphClosure.Construction.graphClosureToP j a
  have : IsReduced Z.left := GraphClosure.Construction.graphClosure_reduced j a
  have : IsProper Z.hom := GraphClosure.Construction.graphClosure_proper j a
  have : IsDominant d.left := (GraphClosure.Construction.graphClosureLift_dense_open j a).2
  have hdp : d ≫ p = j := by
    apply Over.OverMorphism.ext
    exact GraphClosure.Construction.graphClosureLift_toX j a
  have hdq : d ≫ q = a := by
    apply Over.OverMorphism.ext
    exact GraphClosure.Construction.graphClosureLift_toP j a
  have : IsClosedImmersion (pullback.lift p.left q.left (p.w.trans q.w.symm)) := by
    have h : pullback.lift p.left q.left (p.w.trans q.w.symm) =
        (GraphClosure.Construction.rationalGraph j a).imageι := by
      apply pullback.hom_ext
      · exact pullback.lift_fst _ _ _
      · exact pullback.lift_snd _ _ _
    rw [h]
    exact inferInstanceAs (IsClosedImmersion (GraphClosure.Construction.rationalGraph j a).ker.subschemeι)
  exact closed_graph_projection_of_chart_cover d p q Q hQ π V hV A k e he
    (fun i ↦ hdp.trans (hj i)) (fun i ↦ by rw [← Category.assoc, hdq]; exact ha i)

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.ChowCriterion.Construction
