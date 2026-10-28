import OAI.AlgebraicGeometry.PELModuli.CMPoints.ClosedCoefficientPeriods
import OAI.AlgebraicGeometry.PELModuli.CMPoints.CountableCompactRelations

/-! # Fixed Coefficient Patch -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedCoefficientPatch

noncomputable section

/-! Countably many rational coefficient comparisons can be reduced to
one fixed comparison on an open patch. The ball coordinate remains an
auxiliary variable, and every vector in the actual kernel image is tested. -/

open Set
open scoped Classical

theorem exists_fixed_coefficient_patch
    {E X V I : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [TopologicalSpace X] [BaireSpace X] [Nonempty X]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [Countable I]
    {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (H : I → Matrix (Fin 3) (Fin 3) E) (e : I → Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (coordinates : I → V →L[ℂ] Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s))
    (kernel : X → V →L[ℂ] V) (hkernel : Continuous kernel)
    (hcover : ∀ q : X, ∃ (i : I) (z : P.Domain), ∀ v : V,
      ClosedCoefficientPeriods.componentPrescribed P (H i) (e i (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val)) (coordinates i (kernel q v))) :
    ∃ (i : I) (O : Set X), IsOpen O ∧ O.Nonempty ∧
      ∀ q ∈ O, ∃ z : P.Domain, ∀ v : V,
        ClosedCoefficientPeriods.componentPrescribed P (H i) (e i (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val)) (coordinates i (kernel q v)) := by
  let : LocallyCompactSpace P.Domain := P.domain_isOpen.locallyCompactSpace
  let R := fun i : I => {q : X × P.Domain | ∀ v : V,
    ClosedCoefficientPeriods.componentPrescribed P (H i) (e i (Geometry.ComplexBall.PrescribedSignsB.lineVector q.2.val)) (coordinates i (kernel q.1 v))}
  have hR : ∀ i, IsClosed (R i) := by
    intro i
    dsimp only [R]
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro v
    exact ClosedCoefficientPeriods.isClosed_componentPrescribed P (H i) (e i)
      (fun q : X × P.Domain => q.2.val)
      (fun q : X × P.Domain => coordinates i (kernel q.1 v))
      (continuous_subtype_val.comp continuous_snd)
      ((coordinates i).continuous.comp ((hkernel.comp continuous_fst).clm_apply continuous_const))
  exact CountableCompactRelations.exists_open_fixed_relation_of_sigmaCompact R hR hcover

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedCoefficientPatch
