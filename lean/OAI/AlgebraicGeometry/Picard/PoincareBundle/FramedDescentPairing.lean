import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FramedDescentScalars

/-! # Framed Descent Pairing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedDescentPairing

noncomputable section

/-! The native character-descent scalar is the same actual ratio of transported line frames used by PoincareBundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits OAI.AlgebraicGeometry.Picard.Homomorphisms.FramedDescentScalars.Construction

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (D : Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent f)
  (e : D.module ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)

/-- Character descent evaluates the ratio of the transported source frame and the target frame. -/
theorem scalar_eq_frameRatio {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) :
    Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar D e q x y hx hy =
      (Line.FrameUnits.frameRatio ((Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e x).symm ≪≫ D.iso q x y hx hy)
        (Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e y).symm).val := by
  change Line.FrameUnits.scalar ((Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e x).inv ≫ D.hom q x y hx hy ≫ (Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e y).hom) =
    Line.FrameUnits.scalar (((Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e x).inv ≫ D.hom q x y hx hy) ≫ (Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e y).hom)
  exact congrArg Line.FrameUnits.scalar (Category.assoc _ _ _).symm

/-- Identifying the actual two line frames identifies the native character value with PoincareBundle's unit-valued pairing. -/
theorem scalar_eq_of_frames {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q)
    (s t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T ≅ (Scheme.Modules.pullback y).obj D.module)
    (hs : (Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e x).symm ≪≫ D.iso q x y hx hy = s)
    (ht : (Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e y).symm = t) : Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar D e q x y hx hy = (Line.FrameUnits.frameRatio s t).val := by
  rw [scalar_eq_frameRatio, hs, ht]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedDescentPairing
