import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.FrameIndependence
import OAI.AlgebraicGeometry.Picard.PoincareBundle.ConcreteKernelPairing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ContainmentMap

/-! # Kernel Pairing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.KernelPairing

noncomputable section

/-!
# The canonical Poincare kernel pairing and restriction to smaller subgroup schemes
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.LineDescent
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.KernelRectangle

variable {S : Scheme.{u}} {A B Z : Over S} [GrpObj A] [GrpObj B] [GrpObj Z]
  (φ : A ⟶ Z) [IsMonHom φ] (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
  (f : A ⟶ B) [IsMonHom f] (hf : Kernel.Scheme.kernelInclusion f ≫ φ = 1)
  (e : (Scheme.Modules.pullback (β_ A A).hom.left).obj (FirstBiextensionFactor.familyLine P φ).sheaf ≅ (FirstBiextensionFactor.familyLine P φ).sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) e = Poincare.TransverseFrames.sourceVertical φ P Dv)

/-- The unit-valued pairing uses the two actual canonical frames on the same line fiber. -/
def value {T : Over S} (k l : T ⟶ Kernel.Scheme.kernelObject f) : Γ(T.left, ⊤)ˣ :=
  ConcreteKernelPairing.Concrete.value f f (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) (Poincare.TransverseFrames.sourceVertical φ P Dv)
    (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hf) (CanonicalPoincare.LineDescent.secondKernelFrames φ P Dh Dv f hf e hv) k l

/-- The actual canonical pairing is natural under every change of test scheme. -/
theorem value_naturality {T T' : Over S} (a : T' ⟶ T) (k l : T ⟶ Kernel.Scheme.kernelObject f) :
    value φ P Dh Dv f hf e hv (a ≫ k) (a ≫ l) = Units.map a.left.appTop.hom (value φ P Dh Dv f hf e hv k l) :=
  ConcreteKernelPairing.Concrete.value_naturality f f (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh)
    (Poincare.TransverseFrames.sourceVertical φ P Dv) (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hf) (CanonicalPoincare.LineDescent.secondKernelFrames φ P Dh Dv f hf e hv) a k l

/-- Any point with the two included kernel coordinates computes the same canonical pairing. -/
theorem value_at {T : Over S} (k l : T ⟶ Kernel.Scheme.kernelObject f) (a : T ⟶ A ⊗ A)
    (hk : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ fst A A) (hl : l ≫ Kernel.Scheme.kernelInclusion f = a ≫ snd A A) :
    value φ P Dh Dv f hf e hv k l =
      Biextension.Compatibility.kernelObstruction (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) (Poincare.TransverseFrames.sourceVertical φ P Dv) f f
        (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hf) (CanonicalPoincare.LineDescent.secondKernelFrames φ P Dh Dv f hf e hv) k l a hk hl := by
  have ha : Biextension.KernelRectangle.crossPoint f f k l = a := by
    apply CartesianMonoidalCategory.hom_ext
    · exact (Biextension.KernelRectangle.crossPoint_fst f f k l).trans hk
    · exact (Biextension.KernelRectangle.crossPoint_snd f f k l).trans hl
  subst a
  rfl

variable (hi : Biextension.Compatibility.Interchange P Dh Dv)
  (hh : Symmetric.TransverseFrames.returnedFirst (FirstBiextensionFactor.familyLine P φ) (Poincare.TransverseFrames.sourceVertical φ P Dv) e =
    Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh)

attribute [local instance] Kernel.Scheme.kernelGroup

/-- Original biextension interchange and symmetry make the canonical pairing bilinear. -/
def pairing (T : Over S) : (T ⟶ Kernel.Scheme.kernelObject f) →* (T ⟶ Kernel.Scheme.kernelObject f) →* Γ(T.left, ⊤)ˣ :=
  ConcreteKernelPairing.Concrete.pairing f f (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) (Poincare.TransverseFrames.sourceVertical φ P Dv)
    (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hf) (CanonicalPoincare.LineDescent.secondKernelFrames φ P Dh Dv f hf e hv)
    (CanonicalPoincare.LineDescent.transverse_frames φ P Dh Dv hi f hf e hv hh) T

/-- Triviality of the canonical bilinear pairing is exactly the isotropy used by effective descent. -/
theorem isotropic_iff :
    Biextension.Compatibility.Isotropic (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) (Poincare.TransverseFrames.sourceVertical φ P Dv) f f
      (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hf) (CanonicalPoincare.LineDescent.secondKernelFrames φ P Dh Dv f hf e hv) ↔
    ∀ (T : Over S) (k l : T ⟶ Kernel.Scheme.kernelObject f), value φ P Dh Dv f hf e hv k l = 1 := by
  constructor
  · intro h T k l
    exact h T k l (Biextension.KernelRectangle.crossPoint f f k l) _ _
  · intro h T k l a hk hl
    exact (value_at φ P Dh Dv f hf e hv k l a hk hl).symm.trans (h T k l)

variable {C : Over S} [GrpObj C] (g : A ⟶ C) [IsMonHom g] (hg : Kernel.Scheme.kernelInclusion g ≫ φ = 1)
  (i : Kernel.Scheme.kernelObject f ⟶ Kernel.Scheme.kernelObject g) (hi' : i ≫ Kernel.Scheme.kernelInclusion g = Kernel.Scheme.kernelInclusion f)

include hi' in
/-- Restriction along an actual subgroup-scheme inclusion gives the smaller canonical pairing. -/
theorem value_restrict {T : Over S} (k l : T ⟶ Kernel.Scheme.kernelObject f) :
    value φ P Dh Dv f hf e hv k l = value φ P Dh Dv g hg e hv (k ≫ i) (l ≫ i) := by
  let a := Biextension.KernelRectangle.crossPoint f f k l
  have hk : (k ≫ i) ≫ Kernel.Scheme.kernelInclusion g = a ≫ fst A A := by
    rw [Category.assoc, hi', Biextension.KernelRectangle.crossPoint_fst]
  have hl : (l ≫ i) ≫ Kernel.Scheme.kernelInclusion g = a ≫ snd A A := by
    rw [Category.assoc, hi', Biextension.KernelRectangle.crossPoint_snd]
  exact (value_at φ P Dh Dv f hf e hv k l a (Biextension.KernelRectangle.crossPoint_fst f f k l).symm
    (Biextension.KernelRectangle.crossPoint_snd f f k l).symm).trans
    ((FrameIndependence.obstruction_eq φ P Dh f g hf hg Dv e hv
      k l (k ≫ i) (l ≫ i) a _ _ hk hl).trans
      (value_at φ P Dh Dv g hg e hv (k ≫ i) (l ≫ i) a hk hl).symm)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.KernelPairing
