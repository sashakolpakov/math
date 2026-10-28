import OAI.RepresentationTheory.Theta.Geometric.PowerPullbackFrames
import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits
import OAI.RepresentationTheory.Theta.Geometric.EqualFrameTransitionGluing

/-! # Line Power Pullback -/

namespace OAI.RepresentationTheory.Theta.Geometric.LinePowerPullback

noncomputable section

/-! Every scheme pullback commutes with the actual tensor powers of a
line bundle. The comparison is glued from the native local frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem tensorPower_pullback_iso_of_frames {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    {ι : Type u} (U : ι → Y.Opens) (hU : iSup U = ⊤)
    (e : ∀ i, M.restrict (U i).ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (U i).toScheme) (n : ℕ) :
    Nonempty ((Scheme.Modules.pullback f).obj (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule M n) ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule ((Scheme.Modules.pullback f).obj M) n) := by
  have hV : (⨆ i, f ⁻¹ᵁ U i) = ⊤ := by
    apply top_unique
    intro x _
    have hx : f x ∈ iSup U := hU.symm ▸ (show f x ∈ (⊤ : Y.Opens) from trivial)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  let a : ∀ i k, Γ(Y, U i ⊓ U k)ˣ := fun i k => IntrinsicFrame.TransitionUnits.frameTransitionUnit M (U i ⊓ U k)
    (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (show U i ⊓ U k ≤ U i from inf_le_left) (e i))
    (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (show U i ⊓ U k ≤ U k from inf_le_right) (e k))
  let ep : ∀ i, ((Scheme.Modules.pullback f).obj (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule M n)).restrict (f ⁻¹ᵁ U i).ι ≅
      AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (f ⁻¹ᵁ U i).toScheme := fun i => PowerPullbackFrames.powerThenPullbackFrame f M (U i) (e i) n
  let eqp : ∀ i, (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule ((Scheme.Modules.pullback f).obj M) n).restrict (f ⁻¹ᵁ U i).ι ≅
      AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (f ⁻¹ᵁ U i).toScheme := fun i => PowerPullbackFrames.pullbackThenPowerFrame f M (U i) (e i) n
  apply EqualFrameTransitionGluing.exists_iso_of_equal_frame_transitions (X := X) (ι := ι)
    ((Scheme.Modules.pullback f).obj (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule M n))
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule ((Scheme.Modules.pullback f).obj M) n) (fun i => f ⁻¹ᵁ U i) hV
    (fun i k => f ⁻¹ᵁ (U i ⊓ U k))
    (fun i k => f.preimage_mono (show U i ⊓ U k ≤ U i from inf_le_left))
    (fun i k => f.preimage_mono (show U i ⊓ U k ≤ U k from inf_le_right))
    (fun _ _ => le_rfl)
    ep eqp
    (fun i k => (f.app (U i ⊓ U k) (a i k : Γ(Y, U i ⊓ U k))) ^ n)
  · intro i k
    dsimp only [ep]
    rw [PowerPullbackFrames.powerThenPullbackFrame_restrict, PowerPullbackFrames.powerThenPullbackFrame_restrict]
    exact PowerPullbackFrames.powerThenPullbackFrame_scalar f M (U i ⊓ U k) _ _ _
      (IntrinsicFrame.TransitionUnits.frameTransitionUnit_spec M (U i ⊓ U k) _ _) n
  · intro i k
    dsimp only [eqp]
    rw [PowerPullbackFrames.pullbackThenPowerFrame_restrict, PowerPullbackFrames.pullbackThenPowerFrame_restrict]
    exact PowerPullbackFrames.pullbackThenPowerFrame_scalar f M (U i ⊓ U k) _ _ _
      (IntrinsicFrame.TransitionUnits.frameTransitionUnit_spec M (U i ⊓ U k) _ _) n

theorem linePower_pullback_iso {X Y : Scheme.{u}} (f : X ⟶ Y) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (n : ℕ) :
    Nonempty (((L.tensorPower n).pullback f).sheaf ≅ ((L.pullback f).tensorPower n).sheaf) := by
  classical
  change Nonempty ((Scheme.Modules.pullback f).obj (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L.sheaf n) ≅
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule ((Scheme.Modules.pullback f).obj L.sheaf) n)
  choose U hx he using L.locallyTrivial
  have hU : iSup U = ⊤ := by
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  exact tensorPower_pullback_iso_of_frames f L.sheaf U hU
    (fun i => (Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app L.sheaf ≪≫ Classical.choice (he i)) n

end

end OAI.RepresentationTheory.Theta.Geometric.LinePowerPullback
