import OAI.AlgebraicGeometry.Picard.PoincareBundle.WeilKernelPairingComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionPairing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionPairingApply

/-! # Weil Canonical Torsion Pairing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.WeilCanonicalTorsionPairing

noncomputable section

/-! The standard Weil pairing and the canonical full-torsion Poincare pairing have the same orthogonality. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle
open OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.LineDescent OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionPairing.Poincare

variable {k : Type} [Field k] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A.scheme)
  (φ : A.scheme ⟶ D.withPicardGroup.abelian) [IsMonHom φ] (n : ℕ)

/-- The included full torsion subgroup gives an actual dual torsion point. -/
theorem dual_torsion : (Kernel.Scheme.kernelInclusion ((𝟙 A.scheme) ^ n) ≫ φ) ^ n = 1 := by
  simpa only [MonObj.comp_pow] using TorsionPairing.Poincare.torsion_annihilation φ n

variable [IsAlgClosed k] [IsFinite φ.left] [Flat φ.left] [Surjective φ.left]
  (hn : 0 < n)
  [IsFinite ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left]
  [Flat ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left]
  [Surjective ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left]
  [LocallyOfFinitePresentation ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left]
  [IsAffine (Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)).left]
  (C : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k))
    (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n))))

/-- Evaluate the standard Weil pairing after the given homomorphism in its dual variable. -/
def weilValue {T : Over (Spec (.of k))}
    (a b : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)) :
    (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.multiplicativeFppfAb (Spec (.of k))).obj.obj (.op T) :=
  WeilKernelPairingComparison.weilValue A D φ n hn C ((𝟙 A.scheme) ^ n)
    (dual_torsion A D φ n) a (b ≫ (Homomorphisms.KernelGroup.Construction.kernelSchemePullbackIso ((𝟙 A.scheme) ^ n)).inv)

variable
  (Dh : FiberwiseMultiplication.Multiplication (fst D.withPicardGroup.abelian A.scheme) (snd D.withPicardGroup.abelian A.scheme)
    (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare))
  (Dv : FiberwiseMultiplication.Multiplication (snd D.withPicardGroup.abelian A.scheme) (fst D.withPicardGroup.abelian A.scheme)
    (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare))
  (hp : Biextension.Compatibility.Interchange (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dh Dv)
  (σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
      (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) (φ ^ n)).sheaf ≅
        (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) (φ ^ n)).sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication
    (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) (φ ^ n))
    (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dh) σ =
      Poincare.TransverseFrames.sourceVertical (φ ^ n) (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dv)
  (hh : Symmetric.TransverseFrames.returnedFirst
    (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) (φ ^ n))
    (Poincare.TransverseFrames.sourceVertical (φ ^ n) (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dv) σ =
      Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dh)

include hp hh

/-- The exact identity condition agrees on all points of the full torsion group scheme. -/
theorem eq_one_iff {T : Over (Spec (.of k))} (a b : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)) :
    weilValue A D φ n hn C a b = 1 ↔
      TorsionPairing.Poincare.torsionPairing φ (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dh Dv n σ hv hp hh T a b = 1 := by
  have ht := CanonicalPoincare.LineDescent.transverse_frames (φ ^ n) (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dh Dv hp
    ((𝟙 A.scheme) ^ n) (TorsionPairing.Poincare.torsion_annihilation φ n) σ hv hh
  have hc := WeilKernelPairingComparison.eq_one_iff A D φ Dh Dv hp n hn C
    ((𝟙 A.scheme) ^ n) (dual_torsion A D φ n)
    (Pulled.KernelFrames.Poincare.kernelFrames (φ ^ n) (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dh ((𝟙 A.scheme) ^ n)
      (TorsionPairing.Poincare.torsion_annihilation φ n))
    (CanonicalPoincare.LineDescent.secondKernelFrames (φ ^ n) (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dh Dv ((𝟙 A.scheme) ^ n)
      (TorsionPairing.Poincare.torsion_annihilation φ n) σ hv) ht.2 ht.1 a
    (b ≫ (Homomorphisms.KernelGroup.Construction.kernelSchemePullbackIso ((𝟙 A.scheme) ^ n)).inv)
  have hb : (b ≫ (Homomorphisms.KernelGroup.Construction.kernelSchemePullbackIso ((𝟙 A.scheme) ^ n)).inv) ≫
      (Homomorphisms.KernelGroup.Construction.kernelSchemePullbackIso ((𝟙 A.scheme) ^ n)).hom = b := by simp
  have he := congrArg (fun z => ConcreteKernelPairing.Concrete.value ((𝟙 A.scheme) ^ n) ((𝟙 A.scheme) ^ n)
    (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) (φ ^ n))
    (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dh)
    (Poincare.TransverseFrames.sourceVertical (φ ^ n) (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dv)
    (Pulled.KernelFrames.Poincare.kernelFrames (φ ^ n) (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dh ((𝟙 A.scheme) ^ n)
      (TorsionPairing.Poincare.torsion_annihilation φ n))
    (CanonicalPoincare.LineDescent.secondKernelFrames (φ ^ n) (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dh Dv ((𝟙 A.scheme) ^ n)
      (TorsionPairing.Poincare.torsion_annihilation φ n) σ hv) a z) hb
  have ha := TorsionPairingApply.value φ (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dh Dv n σ hv hp hh T a b
  exact hc.trans ((congrArg (fun z => z = 1) (he.trans ha.symm)).to_iff)

attribute [local instance] Kernel.Scheme.kernelGroup

/-- Maximal isotropy for the actual standard Weil pairing supplies the full self-annihilation hypothesis used by descent. -/
theorem selfAnnihilating {H : Over (Spec (.of k))} (i : H ⟶ Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n))
    (hlag : ∀ (T : Over (Spec (.of k))) (y : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)),
      (∀ (U : Over (Spec (.of k))) (a : U ⟶ T) (x : U ⟶ H),
        weilValue A D φ n hn C (x ≫ i) (a ≫ y) = 1) ↔ ∃ x : T ⟶ H, x ≫ i = y) :
    NaturalPairingOrthogonal.SelfAnnihilating i
      (TorsionPairing.Poincare.torsionPairing φ (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dh Dv n σ hv hp hh) := by
  intro T y
  constructor
  · intro hy
    apply (hlag T y).mp
    intro U a x
    exact (eq_one_iff A D φ n hn C Dh Dv hp σ hv hh (x ≫ i) (a ≫ y)).mpr (hy U a x)
  · intro hy
    have hw := (hlag T y).mpr hy
    intro U a x
    exact (eq_one_iff A D φ n hn C Dh Dv hp σ hv hh (x ≫ i) (a ≫ y)).mp (hw U a x)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.WeilCanonicalTorsionPairing
