import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas
import OAI.RepresentationTheory.Theta.Geometric.FrameTransitionUnitCoherence

/-! # Frame Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The section coordinates used by ChernClass agree with the coordinates of
the actual native frame on the equivalent over-site. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme.{0}} (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme)

theorem Intrinsic.FrameCoordinates.frameOnImage_over (W : U.toScheme.Opens) (x : Γ(M, U.ι ''ᵁ W)) :
    DivisorClass.Chern.FramesFrame.Construction.frameOnImage M U e W x =
      (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e).hom.val.app
        (.op (U.overEquivalence.inverse.obj W)) x := by
  have h := Functor.FullyFaithful.map_preimage (Scheme.Modules.overEquiv U).fullyFaithfulFunctor
    (((Scheme.Modules.overFunctorEquiv U).app M ≪≫ e ≪≫
      (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm).hom)
  have hv := congrArg (fun f => f.val.app (.op W) x) h
  exact hv.symm

theorem Intrinsic.FrameCoordinates.transportFrame_over {A B : X.Opens} (h : A = B) (hA : A ≤ U) (hB : B ≤ U)
    (a : Γ(M, A) ≃ₗ[Γ(X, A)] Γ(X, A))
    (ha : ∀ x, a x = (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e).hom.val.app
      (.op (Over.mk (homOfLE hA))) x) (x : Γ(M, B)) :
    DivisorClass.Chern.FramesFrame.Construction.transportFrame M h a x =
      (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e).hom.val.app
        (.op (Over.mk (homOfLE hB))) x := by
  subst B
  exact ha x

theorem Intrinsic.FrameCoordinates.frameOnOpen_over (V : X.Opens) (hV : V ≤ U) (x : Γ(M, V)) :
    DivisorClass.Chern.FramesFrame.Construction.frameOnOpen M U e V hV x =
      (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e).hom.val.app
        (.op (Over.mk (homOfLE hV))) x := by
  exact Intrinsic.FrameCoordinates.transportFrame_over M U e (DivisorClass.Chern.FramesFrame.Construction.image_preimage_subopen U hV)
    (leOfHom (U.overEquivalence.inverse.obj (U.ι ⁻¹ᵁ V)).hom) hV
    (DivisorClass.Chern.FramesFrame.Construction.frameOnImage M U e (U.ι ⁻¹ᵁ V)) (Intrinsic.FrameCoordinates.frameOnImage_over M U e (U.ι ⁻¹ᵁ V)) x

theorem Intrinsic.FrameCoordinates.frameOnOpen_native_restrict (V : X.Opens) (hV : V ≤ U) (x : Γ(M, V)) :
    DivisorClass.Chern.FramesFrame.Construction.frameOnOpen M V (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hV e) V le_rfl x =
      DivisorClass.Chern.FramesFrame.Construction.frameOnOpen M U e V hV x := by
  refine (Intrinsic.FrameCoordinates.frameOnOpen_over M V (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hV e) V le_rfl x).trans ?_
  refine Eq.trans ?_ (Intrinsic.FrameCoordinates.frameOnOpen_over M U e V hV x).symm
  erw [SheafCohomology.Projective.OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization]
  rfl

theorem Intrinsic.FrameCoordinates.frameOnOpen_native_scalar
    (g : M.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme) (x : Γ(M, U)) :
    DivisorClass.Chern.FramesFrame.Construction.frameOnOpen M U e U le_rfl x = DivisorClass.Chern.FramesFrame.Construction.frameOnOpen M U g U le_rfl x *
      (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit M U e g : Γ(X, U)) := by
  have h := SheafCohomology.Projective.OverFrameScalarTransfer.overTrivializationOfRestrictIso_hom_eq_comp_scalar M U e g
    (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit M U e g : Γ(X, U)) (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit_spec M U e g)
  rw [Intrinsic.FrameCoordinates.frameOnOpen_over, Intrinsic.FrameCoordinates.frameOnOpen_over]
  have hv := congrArg (fun f => f.val.app (.op (Over.mk (𝟙 U))) x) h
  refine hv.trans ?_
  change (SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U
    (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit M U e g : Γ(X, U))).val.app (.op (Over.mk (𝟙 U)))
      ((SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U g).hom.val.app
        (.op (Over.mk (𝟙 U))) x) = _
  erw [SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd_app_apply]
  change _ * X.presheaf.map (𝟙 (.op U)) (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit M U e g : Γ(X, U)) = _
  rw [X.presheaf.map_id, ConcreteCategory.id_apply]
  congr 3

theorem Intrinsic.FrameCoordinates.frameOnOpen_native_transition
    (g : M.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme) :
    DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit (DivisorClass.Chern.FramesFrame.Construction.frameOnOpen M U e U le_rfl) (DivisorClass.Chern.FramesFrame.Construction.frameOnOpen M U g U le_rfl) =
      RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit M U e g := by
  apply Units.ext
  change DivisorClass.Chern.FramesFrame.Construction.frameOnOpen M U e U le_rfl ((DivisorClass.Chern.FramesFrame.Construction.frameOnOpen M U g U le_rfl).symm 1) = _
  rw [Intrinsic.FrameCoordinates.frameOnOpen_native_scalar, LinearEquiv.apply_symm_apply, one_mul]

theorem LineFrameAtlas.LocalLineFrame.transition_native (s t : LineFrameAtlas.LocalLineFrame M) (W : X.Opens)
    (hs : W ≤ s.domain) (ht : W ≤ t.domain) :
    s.transition t W hs ht = RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit M W
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hs s.frame)
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization ht t.frame) := by
  have he : s.coordinates W hs = DivisorClass.Chern.FramesFrame.Construction.frameOnOpen M W
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hs s.frame) W le_rfl := by
    ext x
    exact (Intrinsic.FrameCoordinates.frameOnOpen_native_restrict M s.domain s.frame W hs x).symm
  have hg : t.coordinates W ht = DivisorClass.Chern.FramesFrame.Construction.frameOnOpen M W
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization ht t.frame) W le_rfl := by
    ext x
    exact (Intrinsic.FrameCoordinates.frameOnOpen_native_restrict M t.domain t.frame W ht x).symm
  change DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit (s.coordinates W hs) (t.coordinates W ht) = _
  rw [he, hg]
  exact Intrinsic.FrameCoordinates.frameOnOpen_native_transition M W _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
