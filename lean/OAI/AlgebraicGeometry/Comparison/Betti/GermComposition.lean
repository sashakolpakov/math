import Mathlib.Topology.Germ

/-! # Germ Composition -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.GermComposition.AnalyticLocal

noncomputable section

/-! Actual composition of function germs as a ring homomorphism, with
its identity, composition, and point-evaluation normalizations. -/

open Filter
open scoped _root_.Topology

variable {X Y Z R : Type*} [Semiring R]
  {l : Filter X} {m : Filter Y} {k : Filter Z}

def germComposition (f : Y → X) (hf : Tendsto f m l) : Germ l R →+* Germ m R where
  toFun a := a.compTendsto f hf
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := by
    induction a, b using Germ.inductionOn₂ with
    | h u v => rfl
  map_mul' a b := by
    induction a, b using Germ.inductionOn₂ with
    | h u v => rfl

theorem germComposition_coe (f : Y → X) (hf : Tendsto f m l) (u : X → R) :
    germComposition f hf (u : Germ l R) = (u ∘ f : Y → R) := rfl

theorem germComposition_id : germComposition (R := R) (l := l) id tendsto_id = RingHom.id _ := by
  ext a
  induction a using Germ.inductionOn with
  | h u => rfl

theorem germComposition_comp (f : Y → X) (hf : Tendsto f m l)
    (g : Z → Y) (hg : Tendsto g k m) :
    (germComposition (R := R) g hg).comp (germComposition f hf) =
      germComposition (f ∘ g) (hf.comp hg) := by
  ext a
  induction a using Germ.inductionOn with
  | h u => rfl

variable [TopologicalSpace X] [TopologicalSpace Y]

theorem germComposition_value (f : Y → X) (y : Y) (hf : ContinuousAt f y)
    (a : Germ (𝓝 (f y)) R) : Germ.value (germComposition f hf a) = Germ.value a := by
  induction a using Germ.inductionOn with
  | h u => rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.GermComposition.AnalyticLocal
