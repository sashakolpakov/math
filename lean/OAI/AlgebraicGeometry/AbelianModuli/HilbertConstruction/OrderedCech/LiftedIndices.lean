import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.FiniteSubsets

/-! # Lifted Indices -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.LiftedIndices

noncomputable section

/-! Lifting the universe of Čech cover indices preserves their ordered tuples and faces. -/

universe u v

def orderedCechIndexULiftEquiv (ι : Type v) [LinearOrder ι] (q : ℕ) :
    Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} ι) q ≃ Ordered.SectionCechIndices.OrderedCechIndex ι q where
  toFun a := ⟨fun k ↦ (a.val k).down, fun _ _ h ↦ a.property h⟩
  invFun a := ⟨fun k ↦ ULift.up (a.val k), fun _ _ h ↦ a.property h⟩
  left_inv a := by apply Subtype.ext; rfl
  right_inv a := by apply Subtype.ext; rfl

theorem orderedCechIndexULiftEquiv_delete {ι : Type v} [LinearOrder ι] {q : ℕ}
    (a : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} ι) (q + 1)) (k : Fin (q + 2)) :
    orderedCechIndexULiftEquiv ι q (a.delete k) =
      (orderedCechIndexULiftEquiv ι (q + 1) a).delete k := rfl

def orderedCechLiftedFinsetEquiv (ι : Type v) [LinearOrder ι] (q : ℕ) :
    Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} ι) q ≃ {s : Finset ι // s.card = q + 1} :=
  (orderedCechIndexULiftEquiv ι q).trans (FiniteSubsets.orderedCechIndexFinsetEquiv ι q)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.LiftedIndices
