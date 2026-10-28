import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.CechShortExact
import Mathlib.Algebra.Homology.HomologySequence

/-! # Cech Cokernel -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.CechCokernel.AffineCechAcyclic

noncomputable section

/-! Positive Čech vanishing on rational affine charts is stable under taking the cokernel of an embedding into an injective sheaf. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))

theorem cokernel (S : ShortComplex (Sheaf (Opens.grothendieckTopology X.left) (ModuleCat R)))
    (hS : S.ShortExact) [Injective S.X₂] (hA : CechAcyclic.AffineCechAcyclic.Acyclic R X S.X₁) : CechAcyclic.AffineCechAcyclic.Acyclic R X S.X₃ := by
  intro A _ _ _ f _ t ht n
  have hC := CechShortExact.AffineCechAcyclic.shortExact R X S A f (fun a : t => a.val) hS hA
  have hI := CechAcyclic.AffineCechAcyclic.injective R X S.X₂ A f t ht n
  have hK := hA A f t ht (n + 1)
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hC.homology_exact₃ (n + 1) (n + 2) (by simp)).isZero_X₂
    (hI.isZero_homology.eq_of_src _ _) (hK.isZero_homology.eq_of_tgt _ _)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.CechCokernel.AffineCechAcyclic
