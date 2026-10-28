import OAI.AlgebraicGeometry.ComplexMultiplication.CM.PeriodTorus

/-! # Period Action -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodAction

noncomputable section

/-! The full ring of CM integers acts on the canonical CM period
lattice and on its actual complex torus by holomorphic homomorphisms. -/

open scoped Classical _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  (Φ : ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E)

def cmPeriodAction : NumberField.RingOfIntegers E →+* Module.End ℂ (ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) :=
  (Algebra.lsmul ℂ ℂ (ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) :
    ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →ₐ[ℂ] Module.End ℂ (ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E)).toRingHom.comp
      (Φ.periodEmbedding.comp (algebraMap (NumberField.RingOfIntegers E) E))

theorem cmPeriodAction_stable (a : NumberField.RingOfIntegers E)
    (v : ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (hv : v ∈ Φ.periodIntegerLattice) :
    cmPeriodAction Φ a v ∈ Φ.periodIntegerLattice := by
  obtain ⟨b, rfl⟩ := (Φ.mem_periodIntegerLattice v).mp hv
  apply (Φ.mem_periodIntegerLattice _).mpr
  refine ⟨a * b, ?_⟩
  change Φ.periodEmbedding ((a : E) * (b : E)) =
    Φ.periodEmbedding (a : E) * Φ.periodEmbedding (b : E)
  exact map_mul Φ.periodEmbedding _ _

def cmQuotientAction : NumberField.RingOfIntegers E →+* AddMonoid.End Φ.periodTorus where
  toFun a := QuotientAddGroup.map Φ.periodIntegerLattice.toAddSubgroup
    Φ.periodIntegerLattice.toAddSubgroup (cmPeriodAction Φ a).toAddMonoidHom
      (cmPeriodAction_stable Φ a)
  map_zero' := by
    apply AddMonoidHom.ext
    intro z
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective z
    change QuotientAddGroup.mk (cmPeriodAction Φ 0 v) = (0 : Φ.periodTorus)
    rw [map_zero]
    rfl
  map_one' := by
    apply AddMonoidHom.ext
    intro z
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective z
    change QuotientAddGroup.mk (cmPeriodAction Φ 1 v) = QuotientAddGroup.mk v
    rw [map_one]
    rfl
  map_add' := by
    intro a b
    apply AddMonoidHom.ext
    intro z
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective z
    change QuotientAddGroup.mk (cmPeriodAction Φ (a + b) v) =
      QuotientAddGroup.mk (cmPeriodAction Φ a v) + QuotientAddGroup.mk (cmPeriodAction Φ b v)
    rw [map_add]
    exact QuotientAddGroup.mk_add _ _ _
  map_mul' := by
    intro a b
    apply AddMonoidHom.ext
    intro z
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective z
    change QuotientAddGroup.mk (cmPeriodAction Φ (a * b) v) =
      QuotientAddGroup.mk (cmPeriodAction Φ a (cmPeriodAction Φ b v))
    rw [map_mul]
    rfl

theorem cmQuotientAction_contMDiff (a : NumberField.RingOfIntegers E) :
    ContMDiff 𝓘(ℂ, ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) 𝓘(ℂ, ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) ∞ (cmQuotientAction Φ a) := by
  apply Φ.contMDiff_of_periodProjection
  exact Φ.periodProjection_contMDiff.comp
    (LinearMap.toContinuousLinearMap (cmPeriodAction Φ a)).contDiff.contMDiff

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodAction
