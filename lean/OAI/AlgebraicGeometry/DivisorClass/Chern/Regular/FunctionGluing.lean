import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Function Gluing -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.FunctionGluing

noncomputable section

section

/-! Regular transition functions on actual scheme opens, with their native restriction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme}

def regularRestriction {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

@[simp] theorem regularRestriction_self (U : X.Opens) (r : Γ(X, U)) :
    regularRestriction (X := X) (le_refl U) r = r := by
  change X.presheaf.map (𝟙 (op U)) r = r
  rw [X.presheaf.map_id]
  rfl

@[simp] theorem regularRestriction_comp {U V W : X.Opens}
    (hVU : V ≤ U) (hWV : W ≤ V) (r : Γ(X, U)) :
    regularRestriction hWV (regularRestriction hVU r) =
      regularRestriction (hWV.trans hVU) r := by
  exact (ConcreteCategory.congr_hom (X.presheaf.map_comp
    (homOfLE hVU).op (homOfLE hWV).op) r).symm

/-- A regular unit cocycle on an actual Zariski open cover. Coordinates change
from frame `i` to frame `j` by multiplication by `transition i j`. -/
structure RegularLineCocycle (X : Scheme) (ι : Type) where
  domain : ι → X.Opens
  covers : iSup domain = ⊤
  transition : ∀ (i j : ι) (W : X.Opens), W ≤ domain i → W ≤ domain j → Γ(X, W)ˣ
  restrict : ∀ (i j : ι) (U W : X.Opens) (hWU : W ≤ U)
    (hi : U ≤ domain i) (hj : U ≤ domain j),
    regularRestriction hWU (transition i j U hi hj : Γ(X, U)) =
      (transition i j W (hWU.trans hi) (hWU.trans hj) : Γ(X, W))
  refl : ∀ (i : ι) (W : X.Opens) (hi : W ≤ domain i), transition i i W hi hi = 1
  cocycle : ∀ (i j k : ι) (W : X.Opens)
    (hi : W ≤ domain i) (hj : W ≤ domain j) (hk : W ≤ domain k),
    transition i j W hi hj * transition j k W hj hk = transition i k W hi hk

end

/-! Gluing and local equality for the original scheme structure sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme}

theorem exists_regularFunction_glue {ι : Type*} (U : ι → X.Opens) (V : X.Opens)
    (hUV : ∀ i, U i ≤ V) (hcover : V ≤ iSup U) (s : ∀ i, Γ(X, U i))
    (hc : ∀ i j, regularRestriction inf_le_left (s i) = regularRestriction inf_le_right (s j)) :
    ∃ g : Γ(X, V), ∀ i, regularRestriction (hUV i) g = s i := by
  obtain ⟨g, hg, _⟩ := X.sheaf.existsUnique_gluing' U V
    (fun i => homOfLE (hUV i)) hcover s hc
  exact ⟨g, hg⟩

theorem regularFunction_eq_of_restrictions {ι : Type*} (U : ι → X.Opens) (V : X.Opens)
    (hUV : ∀ i, U i ≤ V) (hcover : V ≤ iSup U) (s t : Γ(X, V))
    (h : ∀ i, regularRestriction (hUV i) s = regularRestriction (hUV i) t) : s = t := by
  exact X.sheaf.eq_of_locally_eq' U V (fun i => homOfLE (hUV i)) hcover s t h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.FunctionGluing
