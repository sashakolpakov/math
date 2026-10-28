import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.QuotientIntegralSignature
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Discriminant

/-! # Tangent Signature -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! The exact admissible tangent presentation is equivalent to the
explicit CM quotient. Its integral eigenspaces therefore have the
prescribed dimensions. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} (F : Fiber.ReferenceAnalyticFiber P z) (hP : P.IsAdmissible)

include hP in
theorem Fiber.ReferenceAnalyticFiber.canonicalProjection_surjective : Function.Surjective (P.periodProjection z.val) :=
  fun t => ⟨P.periodSection t, P.periodProjection_section hP z.val t⟩

def Fiber.ReferenceAnalyticFiber.quotientCoordinatesEquiv : Fiber.ReferenceTangent s ≃ₗ[ℂ] Datum.RankThreePELDatum.PeriodQuotientCoordinates (s := s) :=
  (F.projection.quotKerEquivOfSurjective F.surjective).symm.trans
    ((Submodule.quotEquivOfEq _ _ (F.kernel.trans (P.periodProjection_kernel hP z).symm)).trans
      ((P.periodProjection z.val).quotKerEquivOfSurjective
        (Fiber.ReferenceAnalyticFiber.canonicalProjection_surjective (z := z) hP)))

theorem Fiber.ReferenceAnalyticFiber.quotientCoordinatesEquiv_projection (v : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) :
    F.quotientCoordinatesEquiv hP (F.projection v) = P.periodProjection z.val v := by
  simp only [Fiber.ReferenceAnalyticFiber.quotientCoordinatesEquiv, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

theorem Fiber.ReferenceAnalyticFiber.quotientCoordinatesEquiv_action (a : NumberField.RingOfIntegers E) (v : Fiber.ReferenceTangent s) :
    F.quotientCoordinatesEquiv hP (F.action a v) =
      P.periodIntegerAction a (F.quotientCoordinatesEquiv hP v) := by
  have hs : Submodule.span ℝ (F.lattice : Set (Fiber.ReferenceTangent s)) = ⊤ := by
    let : CompactSpace (Fiber.ReferenceTangent s ⧸ F.lattice.toIntSubmodule.toAddSubgroup) := F.compact
    exact RepresentationTheory.Theta.Geometric.CompactLattice.span_top_of_compact_quotient F.lattice.toIntSubmodule
  have he : ((F.quotientCoordinatesEquiv hP).toLinearMap.comp (F.action a)).restrictScalars ℝ =
      ((P.periodIntegerAction a).comp (F.quotientCoordinatesEquiv hP).toLinearMap).restrictScalars ℝ := by
    apply LinearMap.ext_on hs
    intro u hu
    obtain ⟨w, _, rfl⟩ := (F.lattice_membership u).mp hu
    change F.quotientCoordinatesEquiv hP
        (F.action a (F.projection (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings w))) =
      P.periodIntegerAction a
        (F.quotientCoordinatesEquiv hP (F.projection (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings w)))
    rw [F.equivariant, F.quotientCoordinatesEquiv_projection hP,
      F.quotientCoordinatesEquiv_projection hP]
    exact (congrArg (P.periodProjection z.val) (NumberTheory.ArithmeticGroups.Action.CongruenceLevel.ambientAction_embedding P.embeddings (a : E) w)).symm.trans
      (P.periodProjection_ambientAction z.val (a : E) (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings w))
  exact DFunLike.congr_fun he v

def Fiber.ReferenceAnalyticFiber.actionEigenSpace (τ : E →+* ℂ) : Submodule ℂ (Fiber.ReferenceTangent s) where
  carrier := {v | ∀ a : NumberField.RingOfIntegers E, F.action a v = τ (a : E) • v}
  zero_mem' a := by rw [map_zero, smul_zero]
  add_mem' hu hv a := by rw [map_add, hu a, hv a, smul_add]
  smul_mem' c v hv a := by rw [map_smul, hv a, smul_comm]

def Fiber.ReferenceAnalyticFiber.actionEigenEquiv (τ : E →+* ℂ) : F.actionEigenSpace τ ≃ₗ[ℂ] P.integralPeriodEigenSpace τ where
  toFun v := ⟨F.quotientCoordinatesEquiv hP v.val, fun a =>
    (F.quotientCoordinatesEquiv_action hP a v.val).symm.trans
      ((congrArg (F.quotientCoordinatesEquiv hP) (v.property a)).trans
        (map_smul (F.quotientCoordinatesEquiv hP) _ _))⟩
  invFun v := ⟨(F.quotientCoordinatesEquiv hP).symm v.val, by
    intro a
    apply (F.quotientCoordinatesEquiv hP).injective
    rw [F.quotientCoordinatesEquiv_action hP, LinearEquiv.apply_symm_apply,
      v.property a, map_smul, LinearEquiv.apply_symm_apply]⟩
  left_inv v := Subtype.ext ((F.quotientCoordinatesEquiv hP).symm_apply_apply v.val)
  right_inv v := Subtype.ext ((F.quotientCoordinatesEquiv hP).apply_symm_apply v.val)
  map_add' u v := Subtype.ext (map_add (F.quotientCoordinatesEquiv hP) u.val v.val)
  map_smul' c v := Subtype.ext (map_smul (F.quotientCoordinatesEquiv hP) c v.val)

include hP in
theorem Fiber.ReferenceAnalyticFiber.actionEigenSpace_finrank (τ : E ≃ₐ[ℚ] E) :
    Module.finrank ℂ (F.actionEigenSpace (P.μ.comp τ.toRingHom)) = P.lieRank τ := by
  rw [(F.actionEigenEquiv hP (P.μ.comp τ.toRingHom)).finrank_eq]
  exact P.integralPeriodEigenSpace_finrank hP τ

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
