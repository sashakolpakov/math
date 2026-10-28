import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ProductChart
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PairSupportDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportDimension
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineSectionFiniteType
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Product Support Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductSupportDimension

noncomputable section

/-! Every irreducible closed support in a product of integral
finite-type schemes has dimension at most the sum of the factor dimensions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct

theorem bound {K : Type} [Field K] {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    (C : IrreducibleCloseds ↥(pullback f g)) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension C (pullback.fst f g ≫ f) ≤
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f + Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g := by
  let z := C.isIrreducible.genericPoint
  have hz : z ∈ C := (C.isIrreducible.isGenericPoint_genericPoint C.isClosed).mem
  obtain ⟨U, hU, hzU, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top (pullback.fst f g z))
  obtain ⟨V, hV, hzV, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top (pullback.snd f g z))
  let : Nonempty U := ⟨⟨pullback.fst f g z, hzU⟩⟩
  let : Nonempty V := ⟨⟨pullback.snd f g z, hzV⟩⟩
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra g V
  let : Algebra.FiniteType K Γ(X, U) := Foundations.Scheme.AffineSectionFiniteType.specSectionScalarAlgebra_finiteType f U hU
  let : Algebra.FiniteType K Γ(Y, V) := Foundations.Scheme.AffineSectionFiniteType.specSectionScalarAlgebra_finiteType g V hV
  let : Algebra.FiniteType K (Γ(X, U) ⊗[K] Γ(Y, V)) :=
    Algebra.FiniteType.trans (R := K) (S := Γ(X, U)) (A := Γ(X, U) ⊗[K] Γ(Y, V))
      inferInstance inferInstance
  let : IsNoetherianRing (Γ(X, U) ⊗[K] Γ(Y, V)) :=
    Algebra.FiniteType.isNoetherianRing K _
  let : NoetherianSpace (Spec (.of (Γ(X, U) ⊗[K] Γ(Y, V)))) := inferInstance
  let j := Affine.ProductChart.map f g U hU V hV
  let : IsOpenImmersion j := Affine.ProductChart.isOpenImmersion f g U hU V hV
  have hzj : z ∈ Set.range j := by
    rw [Affine.ProductChart.range]
    exact ⟨hzU, hzV⟩
  obtain ⟨w, hw⟩ := hzj
  have hC : (j ⁻¹' (C : Set ↥(pullback f g))).Nonempty := ⟨w, by
    change j w ∈ C
    rw [hw]
    exact hz⟩
  let D := Open.SupportDimension.preimage j C hC
  have hd := Open.SupportDimension.dimension j C hC (pullback.fst f g ≫ f)
  rw [← hd, Affine.ProductChart.over_base,
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_affineSections f U hU,
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_affineSections g V hV]
  exact Affine.PairSupportDimension.bound K Γ(X, U) Γ(Y, V) D

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductSupportDimension
