import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ProjectiveBlocks
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.ProjectivePresentation

/-! # Partition Presentation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.PartitionPresentation

noncomputable section

/-! Actual native and relative projective presentations of a scheme
identified with a finite union of projective components. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem projective_partition_native_presentation {I : Type} [Finite I]
    (V : I → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {X : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : ∀ i, (V i).toOver ⟶ X) [IsIso (ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction.overSigmaDesc f).left] :
    Nonempty (Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom) := by
  obtain ⟨n, i, hi, hbase⟩ := IntegralModel.Finite.ProjectiveBlocks.finite_projective_varieties_embedding V
  have : IsClosedImmersion i := hi
  let q := ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction.overSigmaDesc f
  refine ⟨⟨n, inv q.left ≫ i, inferInstance, ?_⟩⟩
  rw [Category.assoc, hbase, ← q.w, IsIso.inv_hom_id_assoc]

theorem native_projective_relative_presentation {X : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom) :
    Nonempty (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) := by
  let i : X ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace ℂ P.ambientDimension :=
    Over.homMk P.embedding P.over_base
  have : IsClosedImmersion i.left := P.closedImmersion
  exact ⟨Affine.ProjectivePresentation.affine_projective_relative_presentation P.ambientDimension i⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.PartitionPresentation
