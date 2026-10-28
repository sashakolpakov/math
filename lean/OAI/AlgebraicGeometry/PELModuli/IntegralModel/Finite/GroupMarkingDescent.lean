import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ParameterDescent
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.FieldMarkingsOf

/-! # Group Marking Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.GroupMarkingDescent

noncomputable section

/-! A finite group of complex points in an arithmetic finite étale group
scheme acquires simultaneous algebraic coordinates after a finite number-
field extension. The actual group law and geometric distinctness descend
through the constructed TorsionQuotient marking parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ)
  (H : Over (Spec (.of K))) [GrpObj H] [IsFinite H.hom] [Etale H.hom]
  (M : Type) [Group M] [Finite M]

/-- Construct all finite-group coordinates over one finite extension,
retaining their group law, every geometric distinctness condition, and
their original complex values. -/
theorem finite_group_marking_descends
    (a : M →* (Over.mk (Spec.map (CommRingCat.ofHom κ)) ⟶ H))
    (ha : Function.Injective a) (N : ℕ) (hN : N ≠ 0) :
    ∃ (B : Base.ArithmeticBaseExtension K κ) (aL : M →* (Over.mk B.fieldExtension ⟶ H)),
      B.denominator = N ∧ Function.Injective aL ∧
        (∀ (L : Type) [Field L] (s : Spec (.of L) ⟶ Spec (.of K))
          (t : Over.mk s ⟶ Over.mk B.fieldExtension), Function.Injective (fun m => t ≫ aL m)) ∧
        ∀ m, B.complexFieldMap ≫ aL m = a m := by
  let : Fintype M := Fintype.ofFinite M
  let P := AbelianScheme.TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.parameter H M
  let p := AbelianScheme.TorsionQuotient.FieldMarkingsOf.FieldMarkings.ofInjective ℂ
    (Spec.map (CommRingCat.ofHom κ)) a ha
  obtain ⟨B, pL, hBN, hpL⟩ := ParameterDescent.finite_parameter_descends κ P p N hN
  let cL := AbelianScheme.TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.points H M _ pL
  have hc : AbelianScheme.TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.baseChange H M cL B.complexFieldMap =
      AbelianScheme.TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.points H M _ p := by
    exact ((AbelianScheme.TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.representable H M).homEquiv_comp
      B.complexFieldMap pL).symm.trans
        (congrArg (AbelianScheme.TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.points H M _) hpL)
  have hvalues (m : M) : B.complexFieldMap ≫ cL.val m = a m := by
    have h := congrArg (fun c => c.val m) hc
    exact h.trans (congrArg (fun f => f m)
      (AbelianScheme.TorsionQuotient.FieldMarkingsOf.FieldMarkings.ofInjective_points ℂ
        (Spec.map (CommRingCat.ofHom κ)) a ha))
  have hinj : Function.Injective cL.val := by
    intro x y hxy
    apply ha
    exact (hvalues x).symm.trans
      ((congrArg (fun f => B.complexFieldMap ≫ f) hxy).trans (hvalues y))
  exact ⟨B, cL.val, hBN, hinj, cL.property, hvalues⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.GroupMarkingDescent
