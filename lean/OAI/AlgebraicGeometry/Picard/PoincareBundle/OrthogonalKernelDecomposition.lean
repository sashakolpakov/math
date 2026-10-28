import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Orthogonal

/-! # Orthogonal Kernel Decomposition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.OrthogonalKernelDecomposition

noncomputable section

/-! The represented full orthogonal gives the actual ambient decomposition of every inverse-image kernel point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Splitting OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeOrthogonalProduct
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility
open OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalPairingOrthogonal OAI.AlgebraicGeometry.Picard.PoincareBundle.SplitKernelPairing

attribute [local instance] Kernel.Scheme.kernelGroup

variable {S : Scheme.{u}} {A B Z N : Over S} [GrpObj A] [GrpObj B] [GrpObj Z]
  [IsCommMonObj A] [IsCommMonObj Z] (φ : A ⟶ Z) [IsMonHom φ]
  (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
  (n : ℕ) (e : (Scheme.Modules.pullback (β_ A A).hom.left).obj (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf ≅
    (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine P (φ ^ n)) (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh) e =
    Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv)
  (hp : Biextension.Compatibility.Interchange P Dh Dv)
  (hh : Symmetric.TransverseFrames.returnedFirst (FirstBiextensionFactor.familyLine P (φ ^ n)) (Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv) e =
    Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh)
  (d : ℕ) (hnd : n.Coprime d)
  (hk : ∀ (T : Over S) (x : T ⟶ A), x ≫ φ = 1 → x ^ d = 1)
  (f : A ⟶ B) [IsMonHom f]
  (i : Kernel.Scheme.kernelObject f ⟶ Kernel.Scheme.kernelObject ((𝟙 A) ^ n))
  (hi : i ≫ Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n) = Kernel.Scheme.kernelInclusion f)
  (hlag : NaturalPairingOrthogonal.SelfAnnihilating i (TorsionPairing.Poincare.torsionPairing φ P Dh Dv n e hv hp hh))
  (t : N ⟶ A) (j : N ⟶ Kernel.Scheme.kernelObject (φ ^ n)) (hj : j ≫ Kernel.Scheme.kernelInclusion (φ ^ n) = t)
  (ho : ∀ (T : Over S) (x : T ⟶ N), x ≫ j ∈
    NaturalPairingOrthogonal.orthogonal ((i ≫ CoprimeOrthogonalProduct.first) ≫ (Kernel.Splitting.kernelProductIso φ n d hnd hk).hom)
      (SplitKernelPairing.fullPairing φ P Dh Dv n e hv hp hh) T)

include hi hlag hj ho

omit [IsMonHom f] in
/-- Full orthogonality yields the actual sum of a quotient-kernel point and an original-polarization-kernel point. -/
theorem decompose (T : Over S) (x : T ⟶ N) :
    ∃ a : T ⟶ Kernel.Scheme.kernelObject f, ∃ b : T ⟶ Kernel.Scheme.kernelObject φ,
      x ≫ t = (a ≫ Kernel.Scheme.kernelInclusion f) * (b ≫ Kernel.Scheme.kernelInclusion φ) := by
  obtain ⟨z, hz⟩ := (Kernel.Orthogonal.orthogonal_iff_product_image φ P Dh Dv n e hv hp hh
    d hnd hk i hlag (x ≫ j)).mp (ho T x)
  refine ⟨z ≫ fst (Kernel.Scheme.kernelObject f) (Kernel.Scheme.kernelObject φ), z ≫ snd (Kernel.Scheme.kernelObject f) (Kernel.Scheme.kernelObject φ), ?_⟩
  have h := congrArg (fun a => a ≫ Kernel.Scheme.kernelInclusion (φ ^ n)) hz
  simp only [Category.assoc, Kernel.Splitting.kernelProductIso_hom_comp_inclusion, MonObj.comp_mul,
    hj] at h
  have hfst := Category.assoc (i ⊗ₘ 𝟙 (Kernel.Scheme.kernelObject φ))
    (fst (Kernel.Scheme.kernelObject ((𝟙 A) ^ n)) (Kernel.Scheme.kernelObject φ)) (Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n))
  have hsnd := Category.assoc (i ⊗ₘ 𝟙 (Kernel.Scheme.kernelObject φ))
    (snd (Kernel.Scheme.kernelObject ((𝟙 A) ^ n)) (Kernel.Scheme.kernelObject φ)) (Kernel.Scheme.kernelInclusion φ)
  rw [tensorHom_fst, Category.assoc, hi] at hfst
  rw [tensorHom_snd, Category.comp_id] at hsnd
  rw [← hfst, ← hsnd] at h
  simpa only [Category.assoc] using h.symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.OrthogonalKernelDecomposition
