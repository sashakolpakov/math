import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.AdjointLift
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.PullbackGenerators

/-! # Adjoint Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.AdjointRecovery

noncomputable section

/-! The map glued from adjoint frame images recovers the prescribed map into the direct image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {ι : Type u} {U : ι → Y.Opens} (D : Transitions.OpenFrameTransitions U) (f : X ⟶ Y)
variable (hU : ∀ y : Y, ∃ i, y ∈ U i)
variable {N : X.Modules} (β : ModuleSheaf.openFrameModuleSheaf D ⟶ (Scheme.Modules.pushforward f).obj N)

theorem openFrameAdjointLift_spec :
    PullbackSheafMap.openFramePullbackAdjoint D f ≫ (Scheme.Modules.pushforward f).map (AdjointLift.openFrameAdjointLift D f hU β) = β := by
  apply Module.BasisIsomorphisms.moduleMap_eq_of_basis (Module.OpenMapGluing.subordinateOpenBasis U) (Module.OpenMapGluing.subordinateOpenBasis_isBasis U hU)
  intro V
  obtain ⟨i, hi⟩ := V.property
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨r, rfl⟩ := (LocalFreeness.openFrameLocalEquiv D V.val i hi).surjective x
  have hg := PullbackGenerators.openFrameSectionPullback_generator D f V.val i hi r
  have hl := AdjointLift.openFrameAdjointLift_generator D f hU β (f ⁻¹ᵁ V.val) i
    ((TopologicalSpace.Opens.map f.base).monotone hi) (f.app V.val r)
  have hv := AdjointLift.adjointFrameImage_preimage D f β V.val i hi
  exact (congrArg ((AdjointLift.openFrameAdjointLift D f hU β).app (f ⁻¹ᵁ V.val)) hg).trans
    (hl.trans ((congrArg (fun a : Γ(N, f ⁻¹ᵁ V.val) => f.app V.val r • a) hv).trans
      (AdjointFrameCompatibility.adjointFrameGenerator_scalar D f β V.val i hi r).symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.AdjointRecovery
