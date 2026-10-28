import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ImmersionFactorization
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Locally Closed Subscheme -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.LocallyClosedSubscheme

noncomputable section

/-! Constructing the reduced induced scheme on an actual locally closed
subset gives its factorization property on all reduced test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem exists_reduced_immersion_with_range (S : Scheme.{0}) (W : Set S)
    (hW : IsLocallyClosed W) :
    ∃ (Z : Scheme.{0}) (j : Z ⟶ S), IsReduced Z ∧ IsImmersion j ∧ Set.range j = W := by
  obtain ⟨U, F, hU, hF, hUF⟩ := hW
  let V : S.Opens := ⟨U, hU⟩
  let K : TopologicalSpace.Closeds V.toScheme := ⟨V.ι ⁻¹' F, hF.preimage V.ι.continuous⟩
  let I := Scheme.IdealSheafData.vanishingIdeal K
  let Y : Over S := Over.mk (I.subschemeι ≫ V.ι)
  let j : (Reduction.reduction Y).left ⟶ S := (Reduction.reductionι Y).left ≫ Y.hom
  have hj : IsImmersion j := by
    change IsImmersion ((Reduction.reductionι Y).left ≫ (I.subschemeι ≫ V.ι))
    infer_instance
  refine ⟨(Reduction.reduction Y).left, j, inferInstance, hj, ?_⟩
  have hI : Set.range I.subschemeι = V.ι ⁻¹' F := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal K
  have hred : Set.range j = Set.range Y.hom := by
    change Set.range (Y.hom ∘ (Reduction.reductionι Y).left) = _
    rw [Set.range_comp, Reduction.reduction_range, Set.image_univ]
  rw [hred]
  change Set.range (V.ι ∘ I.subschemeι) = W
  rw [Set.range_comp, hI, Set.image_preimage_eq_inter_range]
  have hV : Set.range V.ι = U := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [hV, Set.inter_comm]
  exact hUF.symm

theorem exists_reduced_quasicompact_immersion_with_range
    (S : Scheme.{0}) [NoetherianSpace S] (W : Set S) (hW : IsLocallyClosed W) :
    ∃ (Z : Scheme.{0}) (j : Z ⟶ S),
      IsReduced Z ∧ IsImmersion j ∧ QuasiCompact j ∧ Set.range j = W := by
  obtain ⟨Z, j, hZ, hj, hr⟩ := exists_reduced_immersion_with_range S W hW
  let := hj
  let : NoetherianSpace Z := j.isEmbedding.isInducing.noetherianSpace
  exact ⟨Z, j, hZ, hj, inferInstance, hr⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.LocallyClosedSubscheme
