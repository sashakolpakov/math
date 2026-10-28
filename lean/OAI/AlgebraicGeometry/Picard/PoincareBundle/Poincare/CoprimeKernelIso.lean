import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeDescendedKernelIso
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.KernelOrthogonal
import OAI.AlgebraicGeometry.Picard.PoincareBundle.OrthogonalKernelImageChange

/-! # Coprime Kernel Iso -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.CoprimeKernelIso

noncomputable section

/-! Actual Poincare recovery and maximal full-torsion isotropy construct the unchanged coprime polarization kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Splitting OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeOrthogonalProduct
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility
open OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalPairingOrthogonal OAI.AlgebraicGeometry.Picard.PoincareBundle.SplitKernelPairing OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackKernelContainment

attribute [local instance] Kernel.Scheme.kernelGroup

variable {k : Type u} [Field k] {A B D Z : Over (Spec (.of k))}
  [GrpObj A] [GrpObj B] [GrpObj D] [GrpObj Z]
  [IsCommMonObj A] [IsCommMonObj D] [IsCommMonObj Z]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (φ : A ⟶ Z) [IsMonHom φ] (f : A ⟶ B) [IsMonHom f]
  (m : B ⟶ D) [IsMonHom m] (g : D ⟶ Z) [IsMonHom g]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [IsFinite m.left]
  (n d : ℕ) (hnd : n.Coprime d) (h : f ≫ m ≫ g = φ ^ n)
  (v : Z ⟶ D) (hdual : g ≫ v = (𝟙 D) ^ n)
  (hk : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A), x ≫ φ = 1 → x ^ d = 1)
  (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)
  (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
  (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf ≅
    (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine P (φ ^ n)) (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh) σ =
    TransverseFrames.sourceVertical (φ ^ n) P Dv)
  (hp : Biextension.Compatibility.Interchange P Dh Dv)
  (hh : Symmetric.TransverseFrames.returnedFirst (FirstBiextensionFactor.familyLine P (φ ^ n)) (TransverseFrames.sourceVertical (φ ^ n) P Dv) σ =
    Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh)
  (Q : Line.Bundles.LineBundle (D ⊗ B).left)
  (Qh : FiberwiseMultiplication.Multiplication (fst D B) (snd D B) Q) (Qv : FiberwiseMultiplication.Multiplication (snd D B) (fst D B) Q)
  (hq : Biextension.Compatibility.Interchange Q Qh Qv)
  (e : ((FirstBiextensionFactor.familyLine Q m).pullback (f ⊗ₘ f).left).sheaf ≅ (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf)

include hq e

omit [Flat f.left] [Surjective f.left] [IsCommMonObj D] in
/-- Recovery proves full orthogonality for the actual torsion inclusion, with no orthogonality hypothesis on the descended kernel. -/
theorem inverseImage_orthogonal (T : Over (Spec (.of k))) (x : T ⟶ Kernel.Scheme.kernelObject (f ≫ m)) :
    x ≫ PullbackKernelContainment.inverseImageMap f m g (φ ^ n) h ∈
      NaturalPairingOrthogonal.orthogonal (((Kernel.ContainmentMap.torsionMap f n hf) ≫ CoprimeOrthogonalProduct.first) ≫ (Kernel.Splitting.kernelProductIso φ n d hnd hk).hom)
        (SplitKernelPairing.fullPairing φ P Dh Dv n σ hv hp hh) T := by
  have : IsFinite (f ≫ m).left := inferInstanceAs (IsFinite (f.left ≫ m.left))
  have : IsFinite (f ≫ 𝟙 B).left := by simpa only [Category.comp_id] using (inferInstance : IsFinite f.left)
  have : IsFinite (Kernel.Scheme.kernelObject (f ≫ m)).hom := Kernel.Scheme.kernel_isFinite (f ≫ m)
  have : IsAffine (Kernel.Scheme.kernelObject (f ≫ m)).left := isAffine_of_isAffineHom (Kernel.Scheme.kernelObject (f ≫ m)).hom
  have : IsFinite (Kernel.Scheme.kernelObject (f ≫ 𝟙 B)).hom := Kernel.Scheme.kernel_isFinite (f ≫ 𝟙 B)
  have : IsAffine (Kernel.Scheme.kernelObject (f ≫ 𝟙 B)).left := isAffine_of_isAffineHom (Kernel.Scheme.kernelObject (f ≫ 𝟙 B)).hom
  let jN := PullbackKernelContainment.inverseImageMap f m g (φ ^ n) h
  let jH := PullbackKernelContainment.quotientKernelMap f m g (φ ^ n) h
  let i := Kernel.ContainmentMap.torsionMap f n hf
  let q := (i ≫ CoprimeOrthogonalProduct.first) ≫ (Kernel.Splitting.kernelProductIso φ n d hnd hk).hom
  let r := Kernel.ContainmentMap.map f (f ≫ 𝟙 B)
    (fun _T y hy => by simpa only [Category.comp_id] using hy)
  have hq' : q ≫ Kernel.Scheme.kernelInclusion (φ ^ n) = Kernel.Scheme.kernelInclusion f := by
    dsimp only [q]
    rw [Category.assoc, Category.assoc, Kernel.SplitInclusions.first_inclusion]
    exact Kernel.ContainmentMap.torsionMap_inclusion f n hf
  have ht := KernelOrthogonal.mem_orthogonal f m (φ ^ n) P Dh Dv hp Q Qh Qv hq
    (PullbackKernelContainment.inverseImage_annihilation f m g (φ ^ n) h) (PullbackKernelContainment.quotientKernel_annihilation f m g (φ ^ n) h)
    σ hv hh e jH jN (PullbackKernelContainment.quotientKernelMap_inclusion f m g (φ ^ n) h)
    (PullbackKernelContainment.inverseImageMap_inclusion f m g (φ ^ n) h) x
  exact OrthogonalKernelImageChange.of_inclusions (SplitKernelPairing.fullPairing φ P Dh Dv n σ hv hp hh)
    f (f ≫ 𝟙 B) q jH (Kernel.Scheme.kernelInclusion (φ ^ n)) r
    (Kernel.ContainmentMap.map_inclusion f (f ≫ 𝟙 B) _) hq'
    (PullbackKernelContainment.quotientKernelMap_inclusion f m g (φ ^ n) h) (x ≫ jN) ht

variable (hlag : NaturalPairingOrthogonal.SelfAnnihilating (Kernel.ContainmentMap.torsionMap f n hf)
  (TorsionPairing.Poincare.torsionPairing φ P Dh Dv n σ hv hp hh))

/-- Coprimality and maximal full-torsion isotropy identify the actual original and descended kernels. -/
def kernelIso : Kernel.Scheme.kernelObject φ ≅ Kernel.Scheme.kernelObject m :=
  CoprimeDescendedKernelIso.kernelIso φ f m g n d hnd h v hdual hk hf P Dh Dv σ hv hp hh hlag
    (inverseImage_orthogonal φ f m g n d hnd h hk hf P Dh Dv σ hv hp hh Q Qh Qv hq e)

/-- The kernel isomorphism is the original quotient restricted to the original polarization kernel. -/
theorem kernelIso_hom : (kernelIso φ f m g n d hnd h v hdual hk hf P Dh Dv σ hv hp hh Q Qh Qv hq e hlag).hom =
    CoprimeKernelEmbedding.map φ f m g n d hnd h v hdual hk := rfl

/-- The actual kernel isomorphism preserves the represented group laws. -/
instance kernelIso_isMonHom :
    IsMonHom (kernelIso φ f m g n d hnd h v hdual hk hf P Dh Dv σ hv hp hh Q Qh Qv hq e hlag).hom := by
  rw [kernelIso_hom]
  infer_instance

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.CoprimeKernelIso
