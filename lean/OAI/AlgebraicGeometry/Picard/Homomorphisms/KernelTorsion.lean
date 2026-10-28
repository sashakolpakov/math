import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelGroup
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteFrobeniusTorsion

/-! # Kernel Torsion -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelTorsion

noncomputable section

/-! The entire Frobenius kernel of a smooth commutative group over a
perfect field is killed by p, including its infinitesimal structure. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
variable (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A] [Smooth A.hom]

/-- No ordinary splitting is needed for containment in scheme-theoretic p-torsion. -/
theorem relativeFrobenius_kernel_killed :
    (𝟙 (Kernel.Construction.kernelScheme (Frobenius.Construction.relativeFrobenius p Fact.out
      (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) A))) ^ p = 1 := by
  let hS := Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)
  let F := Frobenius.Construction.relativeFrobenius p Fact.out hS A
  let G : Grp (Over (Spec (.of k))) := ⟨Kernel.Construction.kernelScheme F⟩
  have hfinite := Kernel.Construction.kernelScheme_finiteLocallyFree F
    (Quotient.Construction.relativeFrobenius_finiteLocallyFree_quotient p Fact.out hS A).1
  have : IsFinite G.X.hom := hfinite.1
  exact FiniteFrobeniusTorsion.Construction.finiteGroup_killed_of_trivial_frobenius p k G
    (KernelGroup.Construction.relativeFrobenius_kernel_frobenius p Fact.out hS A)

theorem relativeFrobenius_kernelInclusion_killed :
    (Kernel.Construction.kernelInclusion (Frobenius.Construction.relativeFrobenius p Fact.out
      (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) A)) ^ p = 1 := by
  let F := Frobenius.Construction.relativeFrobenius p Fact.out
    (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) A
  have h := congrArg (fun f => f ≫ Kernel.Construction.kernelInclusion F)
    (relativeFrobenius_kernel_killed p k A)
  rw [MonObj.pow_comp, Category.id_comp, MonObj.one_comp] at h
  exact h

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelTorsion
