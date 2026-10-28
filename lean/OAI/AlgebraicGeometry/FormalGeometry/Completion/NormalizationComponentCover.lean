import OAI.AlgebraicGeometry.FormalGeometry.Completion.ClopenNormalization
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.FiberComponents

/-! # Normalization Component Cover -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizationComponentCover.Construction

noncomputable section

/-! # Completion: an actual open cover of normalization by normalized connected components -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}} [IsNoetherian X] (f : X ⟶ Y) [IsProper f]

/-- The proper family restricted to the actual connected component of a point. -/
def properComponentFamily (x : X) : (Proper.FiberComponents.Construction.noetherianComponentOpen X x).toScheme ⟶ Y :=
  (Proper.FiberComponents.Construction.noetherianComponentOpen X x).ι ≫ f

instance properComponentFamily_isProper (x : X) : IsProper (properComponentFamily f x) := by
  unfold properComponentFamily
  infer_instance

/-- The inclusion of its actual relative normalization. -/
def properComponentNormalizationMap (x : X) :
    (properComponentFamily f x).normalization ⟶ f.normalization :=
  ClopenNormalization.Construction.clopenNormalizationMap f (Proper.FiberComponents.Construction.noetherianComponentOpen X x) isClosed_connectedComponent

instance properComponentNormalizationMap_isOpenImmersion (x : X) :
    IsOpenImmersion (properComponentNormalizationMap f x) :=
  ClopenNormalization.Construction.clopenNormalizationMap_isOpenImmersion f _ _

@[reassoc]
theorem properComponentNormalizationMap_fromNormalization (x : X) :
    properComponentNormalizationMap f x ≫ f.fromNormalization =
      (properComponentFamily f x).fromNormalization :=
  ClopenNormalization.Construction.clopenNormalizationMap_fromNormalization f _ _

/-- These actual open immersions cover the full normalization. -/
def properComponentNormalizationCover : f.normalization.OpenCover where
  I₀ := X
  X x := (properComponentFamily f x).normalization
  f x := properComponentNormalizationMap f x
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro n
    have : Surjective f.toNormalization := Proper.Normalization.Construction.proper_toNormalization_surjective f
    obtain ⟨x, rfl⟩ := f.toNormalization.surjective n
    refine ⟨x, (properComponentFamily f x).toNormalization ⟨x, mem_connectedComponent⟩, ?_⟩
    change ((properComponentFamily f x).toNormalization ≫ properComponentNormalizationMap f x)
      ⟨x, mem_connectedComponent⟩ = f.toNormalization x
    rw [show (properComponentFamily f x).toNormalization ≫ properComponentNormalizationMap f x =
      (Proper.FiberComponents.Construction.noetherianComponentOpen X x).ι ≫ f.toNormalization from
        ClopenNormalization.Construction.clopenNormalizationMap_toNormalization f _ _]
    rfl

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizationComponentCover.Construction
