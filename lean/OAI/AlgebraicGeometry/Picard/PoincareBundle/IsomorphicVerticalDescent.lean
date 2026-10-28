import OAI.AlgebraicGeometry.Picard.PoincareBundle.IsomorphicCoordinateTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.KernelDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedDescentIso

/-! # Isomorphic Vertical Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.IsomorphicVerticalDescent

noncomputable section

/-! Actual line isomorphisms conjugate native vertical descent and preserve its framed character scalars. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationIso OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FiberIsomorphisms
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.KernelDescent OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData

variable {S : Scheme.{u}} {A X Y : Over S} [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (g : X ⟶ Y) [IsMonHom g]
  (L M : Line.Bundles.LineBundle (A ⊗ X).left) (e : L.sheaf ≅ M.sheaf)
  (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)

/-- The native gluing maps are conjugated by the actual pulled line isomorphisms. -/
theorem hom_conjugation {T : Over S} (q : T ⟶ A ⊗ Y) (x y : T ⟶ A ⊗ X)
    (hx : x ≫ (𝟙 A ⊗ₘ g) = q) (hy : y ≫ (𝟙 A ⊗ₘ g) = q) :
    (Vertical.KernelDescent.nativeDatum g M (FiberwiseMultiplicationIso.transportMultiplication (snd A X) (fst A X) L M e Dv)
      (FiberwiseMultiplicationIso.transportKernelFrames (snd A X) (fst A X) L M e Dv g Kv)).hom
      q.left x.left y.left (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
    (Line.FiberIsomorphisms.fiberIso L M e x).inv ≫ (Vertical.KernelDescent.nativeDatum g L Dv Kv).hom
      q.left x.left y.left (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) ≫ (Line.FiberIsomorphisms.fiberIso L M e y).hom := by
  rw [Vertical.KernelDescent.nativeDatum_hom g M (FiberwiseMultiplicationIso.transportMultiplication (snd A X) (fst A X) L M e Dv)
      (FiberwiseMultiplicationIso.transportKernelFrames (snd A X) (fst A X) L M e Dv g Kv) q x y hx hy,
    Vertical.KernelDescent.nativeDatum_hom g L Dv Kv q x y hx hy]
  exact IsomorphicCoordinateTransport.quotient_transport (snd A X) (fst A X) g
    Biextension.AxisData.replaceSecond Biextension.AxisData.replaceSecond_group Biextension.AxisData.replaceSecond_base L M e Dv Kv x y
    (Vertical.KernelDescent.relation g x y (hx.trans hy.symm))

/-- The actual line isomorphism intertwines the two native descent data. -/
theorem hom_compatible {T : Over S} (q : T ⟶ A ⊗ Y) (x y : T ⟶ A ⊗ X)
    (hx : x ≫ (𝟙 A ⊗ₘ g) = q) (hy : y ≫ (𝟙 A ⊗ₘ g) = q) :
    (Scheme.Modules.pullback x.left).map e.hom ≫
      (Vertical.KernelDescent.nativeDatum g M (FiberwiseMultiplicationIso.transportMultiplication (snd A X) (fst A X) L M e Dv)
        (FiberwiseMultiplicationIso.transportKernelFrames (snd A X) (fst A X) L M e Dv g Kv)).hom
        q.left x.left y.left (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
    (Vertical.KernelDescent.nativeDatum g L Dv Kv).hom q.left x.left y.left
      (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) ≫ (Scheme.Modules.pullback y.left).map e.hom := by
  rw [hom_conjugation g L M e Dv Kv q x y hx hy]
  exact Iso.hom_inv_id_assoc (Line.FiberIsomorphisms.fiberIso L M e x) _

/-- Transported global frames preserve the actual native character values on every test scheme. -/
theorem scalar_eq (s : L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (A ⊗ X).left)
    {T : Over S} (q : T ⟶ A ⊗ Y) (x y : T ⟶ A ⊗ X)
    (hx : x ≫ (𝟙 A ⊗ₘ g) = q) (hy : y ≫ (𝟙 A ⊗ₘ g) = q) :
    Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar
      (Vertical.KernelDescent.nativeDatum g M (FiberwiseMultiplicationIso.transportMultiplication (snd A X) (fst A X) L M e Dv)
        (FiberwiseMultiplicationIso.transportKernelFrames (snd A X) (fst A X) L M e Dv g Kv)) (e.symm ≪≫ s)
      q.left x.left y.left (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
    Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Vertical.KernelDescent.nativeDatum g L Dv Kv) s q.left x.left y.left
      (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) :=
  FramedDescentIso.scalar_eq (Vertical.KernelDescent.nativeDatum g L Dv Kv)
    (Vertical.KernelDescent.nativeDatum g M (FiberwiseMultiplicationIso.transportMultiplication (snd A X) (fst A X) L M e Dv)
      (FiberwiseMultiplicationIso.transportKernelFrames (snd A X) (fst A X) L M e Dv g Kv)) e s
    q.left x.left y.left (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy)
    (hom_compatible g L M e Dv Kv q x y hx hy)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.IsomorphicVerticalDescent
