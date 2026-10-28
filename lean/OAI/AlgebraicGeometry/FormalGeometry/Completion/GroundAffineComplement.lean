import OAI.AlgebraicGeometry.FormalGeometry.Completion.GroundPoleEq
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineRationalExists
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorSection

/-! # Ground Affine Complement -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.GroundAffineComplement

noncomputable section

/-! A finite family of rational functions determines one effective pole divisor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

namespace Construction.GroundFinitePoleDivisor

theorem exists_lineBundle {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of K)) [Smooth f] [GeometricallyIntegral f]
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
    let M := GroundPoleLine.Construction.GroundPoleLineBundle.lineBundle f r
    let t := GroundPoleLine.Construction.GroundPoleLineBundle.canonicalSection f r
    refine ⟨M.tensor L, Quotients.FiniteDescent.BinaryTensorId.Construction.BinaryTensorMap.tensorSection t s, ?_⟩
    intro x
    change x ∈ @AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing X (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M.sheaf L.sheaf)
      (Quotients.FiniteDescent.BinaryTensorId.Construction.BinaryTensorMap.tensorSection t s) ↔ _
    rw [Quotients.FiniteDescent.TensorSection.Construction.TensorSectionLocus.nonvanishing (L := M) (M := L) t s]
    change (x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t ∧ x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) ↔ _
    rw [hs x, GroundPoleEq.Construction.GroundPoleSection.mem_nonvanishing_iff_regular f r x]
    simp only [Finset.mem_insert, forall_eq_or_imp]

end Construction.GroundFinitePoleDivisor

namespace Construction.GroundAffineComplementDivisor

theorem exists_lineBundle {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
    (f : X ⟶ Spec (.of K)) [Smooth f] [GeometricallyIntegral f] (U : X.affineOpens) [Nonempty U.1] :
    ∃ (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf), AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s = U.1 := by
  obtain ⟨T, hT⟩ := Quotients.FiniteDescent.AffineRationalExists.Construction.AffineRationalCoordinates.exists_finset f U
  obtain ⟨L, s, hs⟩ := GroundFinitePoleDivisor.exists_lineBundle f T
  refine ⟨L, s, ?_⟩
  apply SetLike.ext
  intro x
  exact (hs x).trans (hT x).symm

end Construction.GroundAffineComplementDivisor

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.GroundAffineComplement
