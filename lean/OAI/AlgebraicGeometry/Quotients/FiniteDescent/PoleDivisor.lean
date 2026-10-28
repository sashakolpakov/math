import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PoleSectionEq
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorSection

/-! # Pole Divisor -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PoleDivisor.Construction.FinitePoleDivisor

noncomputable section

/-! A finite family of rational functions determines one effective pole divisor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem exists_lineBundle {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of K)) [Smooth f]
    (T : Finset X.functionField) :
    ∃ (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf),
      ∀ x : X, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s ↔
        ∀ r ∈ T, ∃ a : X.presheaf.stalk x, algebraMap _ X.functionField a = r := by
  classical
  induction T using Finset.induction with
  | empty =>
    refine ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X, 𝟙 (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X), ?_⟩
    intro x
    change x ∈ @AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing X (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (𝟙 _) ↔ _
    rw [AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing_of_isIso (𝟙 (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X))]
    simp
  | @insert r T hr ih =>
    obtain ⟨L, s, hs⟩ := ih
    let M := PoleLine.Construction.PoleLineBundle.lineBundle f r
    let t := PoleLine.Construction.PoleLineBundle.canonicalSection f r
    refine ⟨M.tensor L, BinaryTensorId.Construction.BinaryTensorMap.tensorSection t s, ?_⟩
    intro x
    change x ∈ @AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing X (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M.sheaf L.sheaf)
      (BinaryTensorId.Construction.BinaryTensorMap.tensorSection t s) ↔ _
    rw [TensorSection.Construction.TensorSectionLocus.nonvanishing (L := M) (M := L) t s]
    change (x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t ∧ x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) ↔ _
    rw [hs x, PoleSectionEq.Construction.PoleSection.mem_nonvanishing_iff_regular f r x]
    simp only [Finset.mem_insert, forall_eq_or_imp]

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PoleDivisor.Construction.FinitePoleDivisor
