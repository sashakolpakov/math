import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExtendedChartGenerators
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ChartGenerators

/-! # Generating Power Family -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-!
Enlarge an affine section cover by global numerators for all of its chart-ring
generators, in one common positive tensor degree.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} [CompactSpace X] [X.IsSeparated]

/-- A finite affine section cover can be enlarged in a common power so that
each original chart has a surjective projective coordinate evaluation. -/
theorem Line.Bundles.LineBundle.generating_power_family (L : Line.Bundles.LineBundle X) (f : X ⟶ S)
    [IsAffine S] [LocallyOfFiniteType f] {k : ℕ}
    (s : Fin (k + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (ha : ∀ i, IsAffineOpen (Ample.LineBundles.sectionNonvanishing (s i))) :
    ∃ (d : ℕ) (_ : 0 < d) (n : ℕ)
      (q : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ TensorPower.PowerSheaf.tensorPowerModule L.sheaf d))
      (j : Fin (k + 1) → Fin (n + 1)),
      (∀ i, q (j i) = TensorPower.Maps.tensorPowerSection (s i) d) ∧
      ∀ i, Function.Surjective
        (ProjectiveChart.Evaluation.projectiveChartEvaluation ((Ample.LineBundles.sectionNonvanishing (q (j i))).ι ≫ f).appTop.hom
          (fun l => Section.Frames.sectionRatio (q (j i)) (q l)) (j i) (Section.Frames.sectionRatio_self (q (j i)))) := by
  classical
  choose m r hr using fun i => Affine.ChartGenerators.affine_chart_generators f (Ample.LineBundles.sectionNonvanishing (s i)) (ha i)
  let I := (i : Fin (k + 1)) × Fin (m i)
  obtain ⟨d, hd, a, hext⟩ := L.sections_extension_uniform
    (fun p : I => s p.1) (fun p : I => r p.1 p.2)
  let J := Fin (k + 1) ⊕ I
  let e := Fintype.equivFin J
  let q : Fin (Fintype.card J + 1) → (Line.Bundles.structureModule X ⟶ TensorPower.PowerSheaf.tensorPowerModule L.sheaf d) :=
    Fin.cases 0 (fun l => Sum.elim (fun i => TensorPower.Maps.tensorPowerSection (s i) d) a (e.symm l))
  let j (i : Fin (k + 1)) : Fin (Fintype.card J + 1) := (e (Sum.inl i)).succ
  have hq (i : Fin (k + 1)) : q (j i) = TensorPower.Maps.tensorPowerSection (s i) d := by
    simp only [q, j, Fin.cases_succ, Equiv.symm_apply_apply, Sum.elim_inl]
  have hnum (p : I) : q (e (Sum.inr p)).succ = a p := by
    simp only [q, Fin.cases_succ, Equiv.symm_apply_apply, Sum.elim_inr]
  refine ⟨d, hd, Fintype.card J, q, j, hq, fun i => ?_⟩
  apply ExtendedChartGenerators.extended_generators_chart_surjective f (s i) d hd q (j i) (hq i) (m i) (r i) (hr i)
  intro l
  refine ⟨(e (Sum.inr ⟨i, l⟩)).succ, ?_⟩
  exact (congrArg (Global.SectionExtension.PowerExtends (s i) (r i l) d) (hnum ⟨i, l⟩)).mpr (hext ⟨i, l⟩)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
