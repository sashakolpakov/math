import OAI.AlgebraicGeometry.Picard.PoincareBundle.OrthogonalKernelDecomposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.DecompositionQuotient
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeKernelEmbedding
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackKernelContainment

/-! # Coprime Descended Kernel Iso -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeDescendedKernelIso

noncomputable section

/-! The full orthogonal calculation and actual effective quotient identify the coprime descended polarization kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Splitting OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeOrthogonalProduct
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility
open OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalPairingOrthogonal OAI.AlgebraicGeometry.Picard.PoincareBundle.SplitKernelPairing OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackKernelContainment

attribute [local instance] Kernel.Scheme.kernelGroup

variable {S : Scheme.{u}} {A B D Z : Over S} [GrpObj A] [GrpObj B] [GrpObj D] [GrpObj Z]
  [IsCommMonObj A] [IsCommMonObj D] [IsCommMonObj Z]
  (φ : A ⟶ Z) [IsMonHom φ] (f : A ⟶ B) [IsMonHom f]
  (m : B ⟶ D) [IsMonHom m] (g : D ⟶ Z) [IsMonHom g]
  [IsFinite f.left] [Flat f.left] [Surjective f.left]
  (n d : ℕ) (hnd : n.Coprime d) (h : f ≫ m ≫ g = φ ^ n)
  (v : Z ⟶ D) (hdual : g ≫ v = (𝟙 D) ^ n)
  (hk : ∀ (T : Over S) (x : T ⟶ A), x ≫ φ = 1 → x ^ d = 1)
  (hf : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)
  (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
  (e : (Scheme.Modules.pullback (β_ A A).hom.left).obj (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf ≅
    (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine P (φ ^ n)) (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh) e =
    Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv)
  (hp : Biextension.Compatibility.Interchange P Dh Dv)
  (hh : Symmetric.TransverseFrames.returnedFirst (FirstBiextensionFactor.familyLine P (φ ^ n)) (Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv) e =
    Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh)
  (hlag : NaturalPairingOrthogonal.SelfAnnihilating (Kernel.ContainmentMap.torsionMap f n hf)
    (TorsionPairing.Poincare.torsionPairing φ P Dh Dv n e hv hp hh))
  (ho : ∀ (T : Over S) (x : T ⟶ Kernel.Scheme.kernelObject (f ≫ m)),
    x ≫ PullbackKernelContainment.inverseImageMap f m g (φ ^ n) h ∈
      NaturalPairingOrthogonal.orthogonal (((Kernel.ContainmentMap.torsionMap f n hf) ≫ CoprimeOrthogonalProduct.first) ≫ (Kernel.Splitting.kernelProductIso φ n d hnd hk).hom)
        (SplitKernelPairing.fullPairing φ P Dh Dv n e hv hp hh) T)

/-- The actual original kernel and descended kernel are isomorphic, retaining all infinitesimal scheme points. -/
def kernelIso : Kernel.Scheme.kernelObject φ ≅ Kernel.Scheme.kernelObject m := by
  have : Mono (CoprimeKernelEmbedding.map φ f m g n d hnd h v hdual hk) :=
    CoprimeKernelEmbedding.map_mono φ f m g n d hnd h v hdual hk hf
  exact Kernel.DecompositionQuotient.kernelIso f m φ
    (CoprimeKernelEmbedding.map φ f m g n d hnd h v hdual hk)
    (CoprimeKernelEmbedding.map_inclusion φ f m g n d hnd h v hdual hk)
    (OrthogonalKernelDecomposition.decompose φ P Dh Dv n e hv hp hh d hnd hk f
      (Kernel.ContainmentMap.torsionMap f n hf) (Kernel.ContainmentMap.torsionMap_inclusion f n hf) hlag
      (Kernel.Scheme.kernelInclusion (f ≫ m)) (PullbackKernelContainment.inverseImageMap f m g (φ ^ n) h)
      (PullbackKernelContainment.inverseImageMap_inclusion f m g (φ ^ n) h) ho)

/-- The isomorphism's actual forward map is the restriction of the quotient to the original polarization kernel. -/
theorem kernelIso_hom : (kernelIso φ f m g n d hnd h v hdual hk hf P Dh Dv e hv hp hh hlag ho).hom =
    CoprimeKernelEmbedding.map φ f m g n d hnd h v hdual hk := rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeDescendedKernelIso
