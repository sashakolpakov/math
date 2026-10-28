import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ProductSupportRetraction

/-! # Elementary Equation Homotopy -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ElementaryEquationHomotopy.Constructions

noncomputable section

/-! An elementary head change is homotopic through maps of the actual
zero-complement pair. Its pullback on relative cohomology is unchanged. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : TopCat} (n : ℕ) (f : X ⟶ TopCat.of (Fin (n + 1) → ℂ)) (a : X ⟶ TopCat.of ℂ)

def adjustedEquation : X ⟶ TopCat.of (Fin (n + 1) → ℂ) :=
  TopCat.ofHom
    ⟨fun x => Fin.cons (f x 0 + a x) (fun i => f x i.succ), by
      apply continuous_pi
      intro i
      cases i using Fin.cases <;> fun_prop⟩

def headHomotopy : TopCat.Homotopy f (adjustedEquation n f a) where
  toFun z := Fin.cons (f z.2 0 + (z.1.val : ℂ) * a z.2) (fun i => f z.2 i.succ)
  continuous_toFun := by
    apply continuous_pi
    intro i
    cases i using Fin.cases <;> fun_prop
  map_zero_left x := by
    ext i
    cases i using Fin.cases <;> simp
  map_one_left x := by
    ext i
    cases i using Fin.cases <;> simp [adjustedEquation]

variable (ha : ∀ x : X, (∀ i : Fin n, f x i.succ = 0) → a x = 0)

include ha in
theorem headHomotopy_zero_iff (t : unitInterval) (x : X) : headHomotopy n f a (t, x) = 0 ↔ f x = 0 := by
  constructor
  · intro hz
    have htail (i : Fin n) : f x i.succ = 0 := congrFun hz i.succ
    have ha0 := ha x htail
    have hhead := congrFun hz 0
    change f x 0 + (t.val : ℂ) * a x = 0 at hhead
    rw [ha0, mul_zero, add_zero] at hhead
    ext i
    cases i using Fin.cases with
    | zero => exact hhead
    | succ i => exact htail i
  · intro hz
    have ha0 : a x = 0 := ha x (fun i => congrFun hz i.succ)
    ext i
    cases i using Fin.cases with
    | zero =>
      change f x 0 + (t.val : ℂ) * a x = 0
      rw [ha0, mul_zero, add_zero]
      exact congrFun hz 0
    | succ i => exact congrFun hz i.succ

variable (A : Set X) (hf : Set.MapsTo f A ({0} : Set (Fin (n + 1) → ℂ))ᶜ)

include ha hf in
theorem adjustedEquation_mapsTo : Set.MapsTo (adjustedEquation n f a) A ({0} : Set (Fin (n + 1) → ℂ))ᶜ := by
  intro x hx hz
  apply hf hx
  exact (headHomotopy_zero_iff n f a ha 1 x).mp ((headHomotopy n f a).map_one_left x |>.trans hz)

theorem relativeCohomologyMap_head_adjustment (d : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf d =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (adjustedEquation n f a)
        (adjustedEquation_mapsTo n f a ha A hf) d := by
  apply Geometric.RelativeCochainHomotopy.Cohomology.relativeSingularCohomologyMap_eq_of_homotopy (ModuleCat.of ℚ ℚ) hf
    (adjustedEquation_mapsTo n f a ha A hf) (headHomotopy n f a)
  intro t x hx hz
  exact hf hx ((headHomotopy_zero_iff n f a ha t x).mp hz)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ElementaryEquationHomotopy.Constructions
