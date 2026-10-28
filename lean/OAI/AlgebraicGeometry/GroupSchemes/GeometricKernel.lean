import OAI.AlgebraicGeometry.GroupSchemes.CoordinatePoints
import OAI.AlgebraicGeometry.GroupSchemes.KernelIdeal
import OAI.AlgebraicGeometry.GroupSchemes.Tower

/-! # Geometric Kernel -/

namespace OAI.AlgebraicGeometry.GroupSchemes

noncomputable section

/-! The actual all-affine torsion kernel gives the coordinate kernel ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite WithConv
open _root_.CategoryTheory.MonObj

universe u
variable {k : Type u} [Field k]

open OAI.AlgebraicGeometry.GroupSchemes.KernelIdeal.FiniteEtale

/-- A geometric torsion-kernel property determines the kernel of affine pullback. -/
theorem GeometricKernel.FiniteEtale.coordinate_kernel_ideal {G H : FiniteEtale.FiniteCommGroupScheme k}
    (i : G.scheme ⟶ H.scheme) (n : ℕ)
    (hkernel : ∀ (T : CommAlgCat.{u} k) (x : FiniteEtale.affine k T ⟶ H.scheme),
      (∃ y : FiniteEtale.affine k T ⟶ G.scheme, y ≫ i = x) ↔ x ^ n = 1) :
    RingHom.ker (FiniteEtale.FiniteCommGroupScheme.coordinateMap i).toRingHom =
      KernelIdeal.FiniteEtale.augmentationPullback H.coordinateAugmentation (H.coordinatePower n) := by
  apply KernelIdeal.FiniteEtale.kernel_eq_augmentationPullback
  intro T f
  constructor
  · rintro ⟨g, hg⟩
    apply (H.coordinatePoints_pow_eq_one_iff T f n).mp
    apply (hkernel T _).mp
    refine ⟨G.coordinatePoints T (toConv g), ?_⟩
    exact (FiniteEtale.FiniteCommGroupScheme.coordinatePoints_postcomp i T g).symm.trans
      (congrArg (fun a => H.coordinatePoints T (toConv a)) hg)
  · intro hf
    have hp := (H.coordinatePoints_pow_eq_one_iff T f n).mpr hf
    obtain ⟨y, hy⟩ := (hkernel T _).mpr hp
    let g : G.algebra →ₐ[k] T := ((G.coordinatePoints T).symm y).ofConv
    have hg : G.coordinatePoints T (toConv g) = y := (G.coordinatePoints T).apply_symm_apply y
    refine ⟨g, ?_⟩
    apply WithConv.toConv_injective
    apply (H.coordinatePoints T).injective
    exact (FiniteEtale.FiniteCommGroupScheme.coordinatePoints_postcomp i T g).trans
      ((congrArg (fun z => z ≫ i) hg).trans hy)

/-- The first transition in an actual p-divisible tower cuts out the p-torsion ideal. -/
theorem FiniteEtale.PDivisibleGroup.first_kernel_ideal {p h : ℕ} (G : FiniteEtale.PDivisibleGroup k p h) :
    RingHom.ker (FiniteEtale.FiniteCommGroupScheme.coordinateMap (G.inclusion 1)).toRingHom =
      KernelIdeal.FiniteEtale.augmentationPullback (G.level 2).coordinateAugmentation
        ((G.level 2).coordinatePower p) := by
  apply GeometricKernel.FiniteEtale.coordinate_kernel_ideal
  intro T x
  simpa only [pow_one] using G.kernel 1 T x

end

end OAI.AlgebraicGeometry.GroupSchemes
