import OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentFrameTransitions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.PullbackIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.FrameRecognition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Powers

/-! # Nilpotent Frame Reduction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentFrameReduction.Transitions

noncomputable section

/-! The actual line bundle obtained from the lifted transition units
reduces to the specified p-power tensor power of the original bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (p : ℕ) [Fact p.Prime] (n : ℕ)
  {X Y : Scheme.{u}} (f : Y ⟶ X) [IsClosedImmersion f] [X.IsSeparated]
  (hn : ∀ V : X.Opens, (p : Γ(X, V)) ^ (n + 1) = 0)
  (hker : ∀ (V : X.Opens) (_hV : IsAffineOpen V),
    RingHom.ker (f.app V).hom = Ideal.span {(p : Γ(X, V))})
  {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (D : AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.Transitions.OpenFrameTransitions (fun i => f ⁻¹ᵁ U i))

theorem pullback_value (V : Y.Opens) (i j : ι)
    (hi : V ≤ f ⁻¹ᵁ U i) (hj : V ≤ f ⁻¹ᵁ U j) :
    (((NilpotentFrameTransitions.transitions p n f hn hker U hU D).pullback f).value V i j hi hj) =
      D.value V i j hi hj ^ (p ^ n) := by
  change Units.map (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.SectionPullback.openSectionPullback f (U i ⊓ U j) V (le_inf hi hj)).toMonoidHom
    (NilpotentFrameTransitions.value p n f hn hker U hU D (U i ⊓ U j) i j inf_le_left inf_le_right) = _
  rw [NilpotentFrameTransitions.value_affine p n f hn hker U hU D (U i ⊓ U j) ((hU i).inf (hU j))]
  apply Units.ext
  change Y.presheaf.map (homOfLE (le_inf hi hj)).op
    (f.app (U i ⊓ U j) (Closed.PowerLift.units p n f hn hker (U i ⊓ U j)
      ((hU i).inf (hU j)) (D.value _ i j _ _)).val) = _
  have hred := congrArg Units.val (Closed.PowerLift.units_reduction p n f hn hker
    (U i ⊓ U j) ((hU i).inf (hU j)) (D.value _ i j
      ((TopologicalSpace.Opens.map f.base).monotone inf_le_left)
      ((TopologicalSpace.Opens.map f.base).monotone inf_le_right)))
  simp only [Units.coe_map, Units.val_pow_eq_pow_val] at hred
  refine (congrArg (fun a : Γ(Y, f ⁻¹ᵁ (U i ⊓ U j)) =>
    Y.presheaf.map (homOfLE (le_inf hi hj)).op a) hred).trans ?_
  rw [(Y.presheaf.map (homOfLE (le_inf hi hj)).op).hom.map_pow]
  exact congrArg (fun a : Γ(Y, V) => a ^ (p ^ n))
    (D.restrict (f ⁻¹ᵁ (U i ⊓ U j)) V (le_inf hi hj) i j
      ((TopologicalSpace.Opens.map f.base).monotone inf_le_left)
      ((TopologicalSpace.Opens.map f.base).monotone inf_le_right))

theorem transitions_pullback :
    (NilpotentFrameTransitions.transitions p n f hn hker U hU D).pullback f = D.power (p ^ n) := by
  have hv : ((NilpotentFrameTransitions.transitions p n f hn hker U hU D).pullback f).value =
      (D.power (p ^ n)).value := by
    funext V i j hi hj
    exact pullback_value p n f hn hker U hU D V i j hi hj
  suffices h : ∀ E F : AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.Transitions.OpenFrameTransitions (fun i => f ⁻¹ᵁ U i),
      E.value = F.value → E = F from h _ _ hv
  intro E F h
  cases E
  cases F
  cases h
  rfl

def lineBundle_pullbackIso (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    ((NilpotentFrameTransitions.lineBundle p n f hn hker U hU D hcover).pullback f).sheaf ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule (AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.ModuleSheaf.openFrameModuleSheaf D) (p ^ n) :=
  AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.PullbackIsomorphism.openFramePullbackIso (NilpotentFrameTransitions.transitions p n f hn hker U hU D) f hcover ≪≫
    eqToIso (congrArg AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.ModuleSheaf.openFrameModuleSheaf (transitions_pullback p n f hn hker U hU D)) ≪≫
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.FrameRecognition.openFrameTensorPowerIso D (AlgebraicGeometry.AbelianModuli.HilbertConstruction.PulledBackFrameTransitions.OpenFrameTransitions.pullback_cover f hcover) (p ^ n)).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentFrameReduction.Transitions
