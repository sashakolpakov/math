import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescription

/-! # Intrinsic Multiplication Point Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationPointComparison.Construction

noncomputable section

/-! Original HilbertConstruction torsion points and the native multiplication kernel
give the same sections of the actual CartierDuality torsion sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem multiplicationKernelSheafIso_point {S : Scheme} (G : Grp (Over S))
    [IsCommMonObj G.X] (n : ℕ) (T : Over S)
    (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 G.X) ^ n)) :
    (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso G n).hom.hom.app (.op T) (ULift.up x) =
      (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso G n).hom.hom.app (.op T) (ULift.up x) :=
  congrArg ((CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso G n).hom.hom.app (.op T))
    (congrArg ULift.up (Category.comp_id x))

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (n : ℕ)

def originalMultiplicationKernelPoint (T : Over S) (x : (A.torsionFunctor n).obj (.op T)) :
    T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n) :=
  (IntrinsicTorsionFunctor.Construction.multiplicationKernelYonedaIso A n).inv.app (.op T) x

theorem originalMultiplicationKernelPoint_inclusion (T : Over S)
    (x : (A.torsionFunctor n).obj (.op T)) :
    originalMultiplicationKernelPoint A n T x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A.scheme) ^ n) = x.val := by
  have he := congrArg Subtype.val
    (ConcreteCategory.congr_hom (NatTrans.congr_app (IntrinsicTorsionFunctor.Construction.multiplicationKernelYonedaIso A n).inv_hom_id (.op T)) x)
  exact (IntrinsicTorsionFunctor.Construction.multiplicationKernelYonedaIso_value A n T (originalMultiplicationKernelPoint A n T x)).symm.trans he

theorem originalMultiplicationKernelPoint_native (T : Over S)
    (x : (A.torsionFunctor n).obj (.op T)) :
    originalMultiplicationKernelPoint A n T x = (IntrinsicTorsionFunctor.Construction.nativeTorsionYonedaIso A n).inv.app (.op T) x := by
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A.scheme) ^ n)) := inferInstanceAs
    (Mono (CategoryTheory.Limits.equalizer.ι ((𝟙 A.scheme) ^ n) 1))
  have hn := congrArg Subtype.val
    (ConcreteCategory.congr_hom (NatTrans.congr_app (IntrinsicTorsionFunctor.Construction.nativeTorsionYonedaIso A n).inv_hom_id (.op T)) x)
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A.scheme) ^ n))).mp
  exact (originalMultiplicationKernelPoint_inclusion A n T x).trans
    ((IntrinsicTorsionFunctor.Construction.nativeTorsionYonedaIso_value A n T ((IntrinsicTorsionFunctor.Construction.nativeTorsionYonedaIso A n).inv.app (.op T) x)).symm.trans hn).symm

theorem originalTorsionSheafPoint_kernel {k : Type} [Field k]
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (n : ℕ) (T : Over (Spec (.of k)))
    (x : (A.torsionFunctor n).obj (.op T)) :
    Prescription.Construction.originalTorsionSheafPoint A n T x =
      (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A.scheme) n).hom.hom.app (.op T)
        (ULift.up (originalMultiplicationKernelPoint A n T x)) := by
  exact (congrArg (fun z => (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk A.scheme) n).hom.hom.app (.op T)
      (ULift.up z)) (originalMultiplicationKernelPoint_native A n T x)).symm.trans
    (multiplicationKernelSheafIso_point (Grp.mk A.scheme) n T (originalMultiplicationKernelPoint A n T x)).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationPointComparison.Construction
