import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleFrameLocal
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.OpenMapGluing

/-! # Image Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Compatible images of actual local frames determine a unique module-sheaf morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens} {D : OpenFrame.Transitions.OpenFrameTransitions U}
variable {M N : X.Modules} (E : CompatibleSheaf.CompatibleSheafFrames D M) (F : CompatibleFrameLocal.CompatibleFrameImages D N)

def CompatibleFrameLocal.CompatibleFrameImages.basisMap : Module.MapBasisExtension.ModuleBasisMap (Module.OpenMapGluing.subordinateOpenBasis U) M N where
  app V := F.localMap E V.val (Classical.choose V.property) (Classical.choose_spec V.property)
  naturality V W h x := F.localMap_restrict E W.val V.val h
    (Classical.choose V.property) (Classical.choose W.property)
    (Classical.choose_spec V.property) (Classical.choose_spec W.property) x

def CompatibleFrameLocal.CompatibleFrameImages.glue (hU : ∀ x : X, ∃ i, x ∈ U i) : M ⟶ N :=
  (F.basisMap E).extend (Module.OpenMapGluing.subordinateOpenBasis_isBasis U hU)

theorem CompatibleFrameLocal.CompatibleFrameImages.glue_app (hU : ∀ x : X, ∃ i, x ∈ U i) (V : X.Opens) (i : ι) (hi : V ≤ U i) (x : Γ(M, V)) :
    (F.glue E hU).app V x = F.localMap E V i hi x := by
  let W : Module.OpenMapGluing.SubordinateOpenIndex U := ⟨V, i, hi⟩
  exact ((F.basisMap E).extend_app (Module.OpenMapGluing.subordinateOpenBasis_isBasis U hU) W x).trans
    (LinearMap.congr_fun (F.localMap_independent E V (Classical.choose W.property) i
      (Classical.choose_spec W.property) hi) x)

theorem CompatibleFrameLocal.CompatibleFrameImages.glue_frame (hU : ∀ x : X, ∃ i, x ∈ U i) (V : X.Opens) (i : ι) (hi : V ≤ U i) (r : Γ(X, V)) :
    (F.glue E hU).app V (E.frame V i hi r) = r • F.value V i hi := by
  exact (F.glue_app E hU V i hi _).trans
    (congrArg (fun a : Γ(X, V) => a • F.value V i hi) ((E.frame V i hi).symm_apply_apply r))

theorem CompatibleFrameLocal.CompatibleFrameImages.glue_unique (hU : ∀ x : X, ∃ i, x ∈ U i) (φ : M ⟶ N)
    (hφ : ∀ (V : X.Opens) (i : ι) (hi : V ≤ U i) (r : Γ(X, V)),
      φ.app V (E.frame V i hi r) = r • F.value V i hi) : φ = F.glue E hU := by
  apply Module.BasisIsomorphisms.moduleMap_eq_of_basis (Module.OpenMapGluing.subordinateOpenBasis U) (Module.OpenMapGluing.subordinateOpenBasis_isBasis U hU)
  intro V
  obtain ⟨i, hi⟩ := V.property
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨r, rfl⟩ := (E.frame V.val i hi).surjective x
  exact (hφ V.val i hi r).trans (F.glue_frame E hU V.val i hi r).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
