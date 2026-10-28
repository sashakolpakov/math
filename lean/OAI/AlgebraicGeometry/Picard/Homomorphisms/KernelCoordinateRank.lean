import OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusKernelRank
import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelGroup
import Mathlib.AlgebraicGeometry.Group.Affine

/-! # Kernel Coordinate Rank -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelCoordinateRank

noncomputable section

/-! The rank of the actual Frobenius kernel equals the dimension of any
of its finite Hopf-coordinate presentations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

theorem finiteHopf_coordinate_finrank (k : Type u) [Field k]
    (R : CommHopfAlgCat k) [Module.Finite k R] (x : PrimeSpectrum k) :
    (((hopfSpec (.of k)).obj (op R)).X).hom.finrank x = Module.finrank k R := by
  change (Spec.map (CommRingCat.ofHom (algebraMap k R))).finrank x = _
  rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  rfl

theorem frobeniusKernel_coordinate_finrank (p : ℕ) (hp : p.Prime)
    (k : Type u) [Field k] (hS : (p : Γ(Spec (.of k), ⊤)) = 0)
    (A : Over (Spec (.of k))) [GrpObj A] (g : ℕ) [SmoothOfRelativeDimension g A.hom]
    (R : CommHopfAlgCat k) [Module.Finite k R]
    (e : ((hopfSpec (.of k)).obj (op R)).X ≅
      Kernel.Construction.kernelScheme (Frobenius.Construction.relativeFrobenius p hp hS A)) : Module.finrank k R = p ^ g := by
  have : Smooth A.hom := SmoothOfRelativeDimension.smooth g A.hom
  let F := Frobenius.Construction.relativeFrobenius p hp hS A
  have hK := Kernel.Construction.kernelScheme_finiteLocallyFree F
    (Quotient.Construction.relativeFrobenius_finiteLocallyFree_quotient p hp hS A).1
  have : Flat (Kernel.Construction.kernelScheme F).hom := hK.2.1
  have : IsFinite (Kernel.Construction.kernelScheme F).hom := hK.1
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget (Spec (.of k))).map e.hom))
  let x : PrimeSpectrum k := ⟨⊥, inferInstance⟩
  calc
    Module.finrank k R = (((hopfSpec (.of k)).obj (op R)).X).hom.finrank x :=
      (finiteHopf_coordinate_finrank k R x).symm
    _ = (Kernel.Construction.kernelScheme F).hom.finrank x := by
      rw [← e.hom.w, Scheme.Hom.finrank_comp_left_of_isIso]
    _ = p ^ g := FrobeniusKernelRank.Construction.relativeFrobenius_kernel_finrank p hp hS A g x

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelCoordinateRank
