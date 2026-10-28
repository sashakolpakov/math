import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.PowerLift
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.FromOpenFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReindexedOpenFrameTransitions
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Nilpotent Frame Transitions -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentFrameTransitions

noncomputable section

/-! An actual frame cocycle on the closed reduction lifts after a
p-power to the ambient p-nilpotent scheme. Affine pair and triple
intersections provide the canonical unit lifts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {X Y : Scheme.{u}}

def restrictUnits (U V : X.Opens) (h : V ≤ U) : Γ(X, U)ˣ →* Γ(X, V)ˣ :=
  Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom

theorem restrictUnits_comp (U V W : X.Opens) (hV : V ≤ U) (hW : W ≤ V) (a : Γ(X, U)ˣ) :
    restrictUnits V W hW (restrictUnits U V hV a) = restrictUnits U W (hW.trans hV) a := by
  apply Units.ext
  exact (ConcreteCategory.congr_hom
    (X.presheaf.map_comp (homOfLE hV).op (homOfLE hW).op) a.val).symm

theorem restrictUnits_id (U : X.Opens) (a : Γ(X, U)ˣ) : restrictUnits U U le_rfl a = a := by
  apply Units.ext
  exact ConcreteCategory.congr_hom (X.presheaf.map_id (Opposite.op U)) a.val

variable (p : ℕ) [Fact p.Prime] (n : ℕ) (f : Y ⟶ X) [IsClosedImmersion f]
  [X.IsSeparated]
  (hn : ∀ V : X.Opens, (p : Γ(X, V)) ^ (n + 1) = 0)
  (hker : ∀ (V : X.Opens) (_hV : IsAffineOpen V),
    RingHom.ker (f.app V).hom = Ideal.span {(p : Γ(X, V))})
  {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (D : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.Transitions.OpenFrameTransitions (fun i => f ⁻¹ᵁ U i))

def value (V : X.Opens) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j) : Γ(X, V)ˣ :=
  restrictUnits (U i ⊓ U j) V (le_inf hi hj)
    (Closed.PowerLift.units p n f hn hker (U i ⊓ U j) ((hU i).inf (hU j))
      (D.value (f ⁻¹ᵁ (U i ⊓ U j)) i j
        ((TopologicalSpace.Opens.map f.base).monotone inf_le_left)
        ((TopologicalSpace.Opens.map f.base).monotone inf_le_right)))

theorem value_restrict (V W : X.Opens) (h : W ≤ V) (i j : ι)
    (hi : V ≤ U i) (hj : V ≤ U j) :
    restrictUnits V W h (NilpotentFrameTransitions.value p n f hn hker U hU D V i j hi hj) =
      NilpotentFrameTransitions.value p n f hn hker U hU D W i j (h.trans hi) (h.trans hj) :=
  restrictUnits_comp _ _ _ _ _ _

theorem value_eq_on (V : X.Opens) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j)
    (W : X.Opens) (hW : IsAffineOpen W) (wi : W ≤ U i) (wj : W ≤ U j) (hVW : V ≤ W) :
    NilpotentFrameTransitions.value p n f hn hker U hU D V i j hi hj =
      restrictUnits W V hVW (Closed.PowerLift.units p n f hn hker W hW
        (D.value (f ⁻¹ᵁ W) i j ((TopologicalSpace.Opens.map f.base).monotone wi)
          ((TopologicalSpace.Opens.map f.base).monotone wj))) := by
  unfold NilpotentFrameTransitions.value
  rw [← restrictUnits_comp (U i ⊓ U j) W V (le_inf wi wj) hVW]
  congr 1
  rw [restrictUnits, Closed.PowerLift.units_restriction p n f hn hker
    (U i ⊓ U j) W ((hU i).inf (hU j)) hW (le_inf wi wj)]
  congr 1
  apply Units.ext
  exact D.restrict (f ⁻¹ᵁ (U i ⊓ U j)) (f ⁻¹ᵁ W)
    ((TopologicalSpace.Opens.map f.base).monotone (le_inf wi wj)) i j
    ((TopologicalSpace.Opens.map f.base).monotone inf_le_left)
    ((TopologicalSpace.Opens.map f.base).monotone inf_le_right)

theorem value_self (V : X.Opens) (i : ι) (hi : V ≤ U i) :
    NilpotentFrameTransitions.value p n f hn hker U hU D V i i hi hi = 1 := by
  rw [value_eq_on p n f hn hker U hU D V i i hi hi (U i) (hU i) le_rfl le_rfl hi,
    D.self, map_one, map_one]

theorem value_affine (V : X.Opens) (hV : IsAffineOpen V) (i j : ι)
    (hi : V ≤ U i) (hj : V ≤ U j) :
    NilpotentFrameTransitions.value p n f hn hker U hU D V i j hi hj =
      Closed.PowerLift.units p n f hn hker V hV
        (D.value (f ⁻¹ᵁ V) i j ((TopologicalSpace.Opens.map f.base).monotone hi)
          ((TopologicalSpace.Opens.map f.base).monotone hj)) := by
  rw [value_eq_on p n f hn hker U hU D V i j hi hj V hV hi hj le_rfl, restrictUnits_id]

theorem value_comp (V : X.Opens) (i j k : ι)
    (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k) :
    NilpotentFrameTransitions.value p n f hn hker U hU D V i j hi hj * NilpotentFrameTransitions.value p n f hn hker U hU D V j k hj hk =
      NilpotentFrameTransitions.value p n f hn hker U hU D V i k hi hk := by
  let W := (U i ⊓ U j) ⊓ U k
  have hW : IsAffineOpen W := ((hU i).inf (hU j)).inf (hU k)
  have wi : W ≤ U i := inf_le_left.trans inf_le_left
  have wj : W ≤ U j := inf_le_left.trans inf_le_right
  have wk : W ≤ U k := inf_le_right
  have hVW : V ≤ W := le_inf (le_inf hi hj) hk
  rw [value_eq_on p n f hn hker U hU D V i j hi hj W hW wi wj hVW,
    value_eq_on p n f hn hker U hU D V j k hj hk W hW wj wk hVW,
    value_eq_on p n f hn hker U hU D V i k hi hk W hW wi wk hVW,
    ← map_mul, ← map_mul, D.comp]

def transitions : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.Transitions.OpenFrameTransitions U where
  value := NilpotentFrameTransitions.value p n f hn hker U hU D
  restrict V W h i j hi hj := congrArg Units.val
    (value_restrict p n f hn hker U hU D V W h i j hi hj)
  self := value_self p n f hn hker U hU D
  comp := value_comp p n f hn hker U hU D

def lineBundle (hcover : ∀ x : X, ∃ i, x ∈ U i) : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X :=
  OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.FromOpenFrames.lineBundleFromOpenFrames (transitions p n f hn hker U hU D) hcover

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentFrameTransitions
