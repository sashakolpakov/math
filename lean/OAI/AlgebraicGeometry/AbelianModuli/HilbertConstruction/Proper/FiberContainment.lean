import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-! # Fiber Containment -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FiberContainment

noncomputable section

/-! A proper family's fibers lie in a prescribed open set over an actual open subset of the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {X S Y : Scheme.{u}}

def properFiberContainmentOpen (p : X ⟶ S) [UniversallyClosed p] (f : X ⟶ Y) (U : Y.Opens) : S.Opens :=
  ⟨(p '' ((f ⁻¹ᵁ U : X.Opens) : Set X)ᶜ)ᶜ,
    (p.isClosedMap _ (f ⁻¹ᵁ U).isOpen.isClosed_compl).isOpen_compl⟩

theorem mem_properFiberContainmentOpen_iff (p : X ⟶ S) [UniversallyClosed p]
    (f : X ⟶ Y) (U : Y.Opens) (s : S) :
    s ∈ properFiberContainmentOpen p f U ↔ ∀ x : X, p x = s → f x ∈ U := by
  constructor
  · intro hs x hx
    by_contra h
    exact hs ⟨x, h, hx⟩
  · intro hs ⟨x, hx, hxs⟩
    exact hx (hs x hxs)

theorem properFiberContainmentOpen_preimage_le (p : X ⟶ S) [UniversallyClosed p]
    (f : X ⟶ Y) (U : Y.Opens) : p ⁻¹ᵁ properFiberContainmentOpen p f U ≤ f ⁻¹ᵁ U := by
  intro x hx
  exact (mem_properFiberContainmentOpen_iff p f U (p x)).mp hx x rfl

theorem le_properFiberContainmentOpen_iff (p : X ⟶ S) [UniversallyClosed p]
    (f : X ⟶ Y) (U : Y.Opens) (V : S.Opens) :
    V ≤ properFiberContainmentOpen p f U ↔ p ⁻¹ᵁ V ≤ f ⁻¹ᵁ U := by
  constructor
  · intro h x hx
    exact properFiberContainmentOpen_preimage_le p f U (h hx)
  · intro h s hs
    apply (mem_properFiberContainmentOpen_iff p f U s).mpr
    intro x hx
    have hpx : p x ∈ V := hx.symm ▸ hs
    exact h hpx

def properFiberContainmentFactor (p : X ⟶ S) [UniversallyClosed p] (f : X ⟶ Y) (U : Y.Opens) :
    (p ⁻¹ᵁ properFiberContainmentOpen p f U).toScheme ⟶ U.toScheme :=
  X.homOfLE (properFiberContainmentOpen_preimage_le p f U) ≫ (f ∣_ U)

theorem properFiberContainmentFactor_comp (p : X ⟶ S) [UniversallyClosed p]
    (f : X ⟶ Y) (U : Y.Opens) :
    properFiberContainmentFactor p f U ≫ U.ι = (p ⁻¹ᵁ properFiberContainmentOpen p f U).ι ≫ f := by
  unfold properFiberContainmentFactor
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, X.homOfLE_ι]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FiberContainment
