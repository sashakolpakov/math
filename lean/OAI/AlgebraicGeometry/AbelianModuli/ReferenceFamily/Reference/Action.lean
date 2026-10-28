import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber
import OAI.RepresentationTheory.Theta.Geometric.Torus.Manifold

/-! # Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! The integral reference action descends holomorphically to the exact
period quotient. Its lattice stability is proved from admissibility. -/

open scoped _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} (F : Fiber.ReferenceAnalyticFiber P z)

theorem Fiber.ReferenceAnalyticFiber.action_preserves_lattice (hP : P.IsAdmissible)
    (a : NumberField.RingOfIntegers E) (v : Fiber.ReferenceTangent s) (hv : v ∈ F.lattice) :
    F.action a v ∈ F.lattice := by
  obtain ⟨w, hw, rfl⟩ := (F.lattice_membership v).mp hv
  rw [F.equivariant]
  apply (F.lattice_membership _).mpr
  rcases hP with ⟨_, _, _, _, _, _, _, _, _, hL, _⟩
  exact ⟨(a : E) • w, hL.2.2 a w hw, rfl⟩

def Fiber.ReferenceAnalyticFiber.quotientAction (hP : P.IsAdmissible) (a : NumberField.RingOfIntegers E) :
    F.periodData.periodTorus →+ F.periodData.periodTorus :=
  QuotientAddGroup.map F.lattice F.lattice (F.action a).toAddMonoidHom
    (fun v hv => F.action_preserves_lattice hP a v hv)

@[simp] theorem Fiber.ReferenceAnalyticFiber.quotientAction_mk (hP : P.IsAdmissible)
    (a : NumberField.RingOfIntegers E) (v : Fiber.ReferenceTangent s) :
    F.quotientAction hP a (QuotientAddGroup.mk v) = QuotientAddGroup.mk (F.action a v) := rfl

theorem Fiber.ReferenceAnalyticFiber.quotientAction_contMDiff (hP : P.IsAdmissible) (a : NumberField.RingOfIntegers E) :
    ContMDiff 𝓘(ℂ, F.periodData.space) 𝓘(ℂ, F.periodData.space) ∞ (F.quotientAction hP a) := by
  apply F.periodData.contMDiff_of_periodProjection
  exact F.periodData.periodProjection_contMDiff.comp
    (LinearMap.toContinuousLinearMap (F.action a)).contDiff.contMDiff

def Fiber.ReferenceAnalyticFiber.quotientRingAction (hP : P.IsAdmissible) :
    NumberField.RingOfIntegers E →+* AddMonoid.End F.periodData.periodTorus where
  toFun := F.quotientAction hP
  map_zero' := by
    ext t
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective t
    change QuotientAddGroup.mk (F.action 0 v) = (0 : F.periodData.periodTorus)
    rw [map_zero]
    rfl
  map_one' := by
    ext t
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective t
    change QuotientAddGroup.mk (F.action 1 v) = QuotientAddGroup.mk v
    rw [map_one]
    rfl
  map_add' := by
    intro a b
    ext t
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective t
    change QuotientAddGroup.mk (F.action (a + b) v) =
      QuotientAddGroup.mk (F.action a v) + QuotientAddGroup.mk (F.action b v)
    rw [map_add]
    exact QuotientAddGroup.mk_add F.lattice (F.action a v) (F.action b v)
  map_mul' := by
    intro a b
    ext t
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective t
    change QuotientAddGroup.mk (F.action (a * b) v) = QuotientAddGroup.mk (F.action a (F.action b v))
    rw [map_mul]
    rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
