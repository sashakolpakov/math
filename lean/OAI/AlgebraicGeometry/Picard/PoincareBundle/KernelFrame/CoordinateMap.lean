import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.PreimageQuotient
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationCoordinateMap

/-! # Coordinate Map -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.CoordinateMap

noncomputable section

/-! Kernel frames restrict through an actual group-coordinate homomorphism and the represented inverse-image kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

attribute [local instance] Kernel.Scheme.kernelGroup

variable {S : Scheme.{u}} {E A B C X : Over S} [GrpObj A] [GrpObj B] [GrpObj C]
  (p : E ⟶ A) (r : E ⟶ X) (f : A ⟶ B) [IsMonHom f] (m : B ⟶ C) [IsMonHom m]
  (L : Line.Bundles.LineBundle E.left) (D : FiberwiseMultiplication.Multiplication (p ≫ f) r L)
  (K : FiberwiseMultiplication.KernelFrames (p ≫ f) r L m D)

/-- The actual inverse-image kernel point has the required image group coordinate. -/
theorem imageKernel {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject (f ≫ m)) (a : T ⟶ E)
    (ha : k ≫ Kernel.Scheme.kernelInclusion (f ≫ m) = a ≫ p) :
    (k ≫ Kernel.PreimageQuotient.map f m) ≫ Kernel.Scheme.kernelInclusion m = a ≫ (p ≫ f) := by
  rw [Category.assoc, Kernel.PreimageQuotient.map_inclusion, ← Category.assoc, ha, Category.assoc]

/-- The complete frame system is pulled to the actual inverse-image kernel. -/
def restrictCoordinate : FiberwiseMultiplication.KernelFrames p r L (f ≫ m)
    (MultiplicationCoordinateMap.restrictCoordinate p r f L D) where
  frame := fun {_T} k a ha => K.frame (k ≫ Kernel.PreimageQuotient.map f m) a (imageKernel p f m k a ha)
  unit := fun {T} a ha hk => by
    change K.frame ((1 : T ⟶ Kernel.Scheme.kernelObject (f ≫ m)) ≫ Kernel.PreimageQuotient.map f m) a _ =
      D.unitFrame a (MultiplicationCoordinateMap.mappedUnit p f a ha)
    simp only [MonObj.one_comp]
    exact K.unit a (MultiplicationCoordinateMap.mappedUnit p f a ha) _
  multiplicative := fun {_T} k l t hkt a b c ha hb hc hab U =>
    K.multiplicative (k ≫ Kernel.PreimageQuotient.map f m) (l ≫ Kernel.PreimageQuotient.map f m)
      (t ≫ Kernel.PreimageQuotient.map f m)
      ((MonObj.mul_comp k l (Kernel.PreimageQuotient.map f m)).symm.trans
        (congrArg (fun z => z ≫ Kernel.PreimageQuotient.map f m) hkt))
      a b c (imageKernel p f m k a ha) (imageKernel p f m l b hb) (imageKernel p f m t c hc)
      (MultiplicationCoordinateMap.mappedRel p r f a b c hab) U
  natural := fun {_T _U} u k k' huk a a' ha ha' hua =>
    K.natural u (k ≫ Kernel.PreimageQuotient.map f m) (k' ≫ Kernel.PreimageQuotient.map f m)
      ((Category.assoc u k (Kernel.PreimageQuotient.map f m)).symm.trans
        (congrArg (fun z => z ≫ Kernel.PreimageQuotient.map f m) huk))
      a a' (imageKernel p f m k a ha) (imageKernel p f m k' a' ha') hua

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.CoordinateMap
