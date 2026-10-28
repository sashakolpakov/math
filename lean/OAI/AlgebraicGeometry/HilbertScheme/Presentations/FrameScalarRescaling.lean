import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FrameTransitionCocycles

/-! # Frame Scalar Rescaling -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.FrameScalarRescaling

noncomputable section

/-! Actual structure-module automorphisms rescale local frames, with
the precise resulting transition function. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X : Scheme.{u}}

def structureScalarAutomorphism (c : Γ(X, ⊤)ˣ) : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X where
  hom := (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv X).symm (c : Γ(X, ⊤))
  inv := (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv X).symm ((c⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤))
  hom_inv_id := by
    change (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv X).symm ((c⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) *
      (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv X).symm (c : Γ(X, ⊤)) = 1
    rw [← map_mul, Units.inv_mul, map_one]
  inv_hom_id := by
    change (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv X).symm (c : Γ(X, ⊤)) *
      (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv X).symm ((c⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) = 1
    rw [← map_mul, Units.mul_inv, map_one]

theorem structureScalarAutomorphism_hom_value (c : Γ(X, ⊤)ˣ) :
    AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (structureScalarAutomorphism c).hom = (c : Γ(X, ⊤)) :=
  (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv X).apply_symm_apply _

theorem structureScalarAutomorphism_inv_value (c : Γ(X, ⊤)ˣ) :
    AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (structureScalarAutomorphism c).inv = ((c⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) :=
  (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv X).apply_symm_apply _

theorem structureModuleEndValue_comp (f g : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) :
    AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (f ≫ g) = AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X f * AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X g :=
  (map_mul (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X) g f).trans (mul_comm _ _)

def rescaleFrame {M : X.Modules} (e : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (c : Γ(X, ⊤)ˣ) :
    M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X := e ≪≫ structureScalarAutomorphism c

theorem frameTransitionValue_rescale {M : X.Modules} (e f : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (c d : Γ(X, ⊤)ˣ) :
    FrameTransitionCocycles.frameTransitionValue (rescaleFrame e c) (rescaleFrame f d) =
      ((c⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) * FrameTransitionCocycles.frameTransitionValue e f * (d : Γ(X, ⊤)) := by
  unfold FrameTransitionCocycles.frameTransitionValue
  change AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (((structureScalarAutomorphism c).inv ≫ e.inv) ≫
      (f.hom ≫ (structureScalarAutomorphism d).hom)) = _
  rw [Category.assoc, ← Category.assoc e.inv f.hom,
    structureModuleEndValue_comp, structureModuleEndValue_comp,
    structureScalarAutomorphism_hom_value, structureScalarAutomorphism_inv_value, mul_assoc]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.FrameScalarRescaling
