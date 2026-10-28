import OAI.NumberTheory.PadicHodge.GeometricComparison.PoleSectionEq
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PoleSectionEq
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorSection

/-! # Pole Divisor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.PoleDivisor.FinitePoleDivisor

noncomputable section

/-! Effective pole divisors for finite rational-function families over arbitrary fields. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem exists_lineBundle {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of K)) [Smooth f] [GeometricallyIntegral f]
    (T : Finset X.functionField) :
    ∃ (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (s : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf),
      ∀ x : X, x ∈ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s ↔
        ∀ r ∈ T, ∃ a : X.presheaf.stalk x, algebraMap _ X.functionField a = r := by
  classical
  induction T using Finset.induction with
  | empty =>
    refine ⟨AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X, 𝟙 (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X), ?_⟩
    intro x
    change x ∈ @AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing X (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (𝟙 _) ↔ _
    rw [AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing_of_isIso (𝟙 (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X))]
    simp
  | @insert r T hr ih =>
    obtain ⟨L, s, hs⟩ := ih
    let M := PoleLine.PoleLineBundle.lineBundle f r
    let t := PoleLine.PoleLineBundle.canonicalSection f r
    refine ⟨M.tensor L, AlgebraicGeometry.Quotients.FiniteDescent.BinaryTensorId.Construction.BinaryTensorMap.tensorSection t s, ?_⟩
    intro x
    change x ∈ @AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing X (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M.sheaf L.sheaf)
      (AlgebraicGeometry.Quotients.FiniteDescent.BinaryTensorId.Construction.BinaryTensorMap.tensorSection t s) ↔ _
    rw [AlgebraicGeometry.Quotients.FiniteDescent.TensorSection.Construction.TensorSectionLocus.nonvanishing (L := M) (M := L) t s]
    change (x ∈ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t ∧ x ∈ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) ↔ _
    rw [hs x, PoleSectionEq.PoleSection.mem_nonvanishing_iff_regular f r x]
    simp only [Finset.mem_insert, forall_eq_or_imp]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.PoleDivisor.FinitePoleDivisor
