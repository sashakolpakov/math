import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Torsion

/-! # Geometric Marking -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GeometricMarking.Construction

noncomputable section

/-!
The transported prime-to-p full marking on the geometric Frobenius
quotient is its actual pulled-back marking. The kernel torsion hypothesis
used in the general level-transport theorem is proved here.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
variable {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))

theorem geometricFrobenius_kernel_killed (T : Over (Spec (.of k))) (x : T ⟶ A.scheme)
    (hx : x ≫ (Torsion.Construction.geometricFrobeniusIsogeny p k A).hom = 1) : x ^ p = 1 := by
  let F := (Torsion.Construction.geometricFrobeniusIsogeny p k A).hom
  let y := (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv F T).symm ⟨x, hx⟩
  have hy : y ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion F = x := congrArg Subtype.val
    ((Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv F T).apply_symm_apply ⟨x, hx⟩)
  exact (congrArg (fun a => a ^ p) hy).symm.trans
    ((MonObj.comp_pow (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion F) p y).symm.trans
      ((congrArg (fun a => y ≫ a) (Torsion.Construction.nativeFrobeniusKernelInclusion_killed p k A)).trans
        (MonObj.comp_one y)))

/-- Full ordered level is compared as a natural isomorphism on every
test scheme, using the proved p-torsion bound on the Frobenius kernel. -/
theorem geometricFrobenius_quotientLevel_eq_pullback {N : ℕ} (hpN : Nat.Coprime p N)
    (level : A.FullLevel N) :
    Power.Construction.quotientLevel (Torsion.Construction.geometricFrobeniusIsogeny p k A) hpN
        (geometricFrobenius_kernel_killed p k A) level =
      level.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p (Fact.out : p.Prime) _
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p))) :=
  Action.Construction.frobenius_quotientLevel_eq_pullback p (Fact.out : p.Prime)
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) hpN
    (geometricFrobenius_kernel_killed p k A) level

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GeometricMarking.Construction
