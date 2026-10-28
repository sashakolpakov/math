import OAI.AlgebraicGeometry.Picard.Homomorphisms.Verschiebung
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GeometricIsogeny

/-! # Frobenius Points -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusPoints

noncomputable section

/-! Frobenius is bijective on geometric points, and its Verschiebung
kernel has exactly the geometric p-torsion point group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable (p : ℕ) (hp : p.Prime) {S : Scheme.{u}} (hS : (p : Γ(S, ⊤)) = 0)
variable (A : Over S) [GrpObj A] [LocallyOfFiniteType A.hom]
variable {K : Type u} [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S)

theorem relativeFrobenius_points_bijective :
    Function.Bijective (IsMonHom.monoidHom (Frobenius.Construction.relativeFrobenius p hp hS A) (Over.mk s)) := by
  let F := Frobenius.Construction.relativeFrobenius p hp hS A
  constructor
  · intro x y h
    apply Over.OverMorphism.ext
    have ht : UniversallyInjective F.left ↔ ∀ (L : Type u) [Field L],
        Function.Injective (fun x : Spec (.of L) ⟶ A.left => x ≫ F.left) :=
      (tfae_universallyInjective F.left).out 1 2
    have hi := ht.mp (inferInstance : UniversallyInjective F.left)
    exact hi K (congrArg Over.Hom.left h)
  · intro y
    obtain ⟨x, hx⟩ := AbelianScheme.FrobeniusKernel.GeometricIsogeny.Construction.exists_geometric_lift F.left y.left
    let z := (AbelianScheme.FrobeniusKernel.GeometricIsogeny.Construction.overGeometricFiberEquiv F s y).symm ⟨x, hx⟩
    exact ⟨z.val, z.property⟩

def relativeFrobeniusPointsEquiv :
    (Over.mk s ⟶ A) ≃* (Over.mk s ⟶ Frobenius.Construction.frobeniusTwist p hp hS A) :=
  MulEquiv.ofBijective (IsMonHom.monoidHom (Frobenius.Construction.relativeFrobenius p hp hS A) (Over.mk s))
    (relativeFrobenius_points_bijective p hp hS A s)

@[simp]
theorem relativeFrobeniusPointsEquiv_apply (x : Over.mk s ⟶ A) :
    relativeFrobeniusPointsEquiv p hp hS A s x = x ≫ Frobenius.Construction.relativeFrobenius p hp hS A := rfl

section Kernels

variable {G H : Type u} [CommGroup G] [Group H]

def powerFactorKernelEquiv (e : G ≃* H) (v : H →* G) (n : ℕ)
    (hv : ∀ x : G, v (e x) = x ^ n) : v.ker ≃* (powMonoidHom n : G →* G).ker where
  toFun y := ⟨e.symm y.val, by
    change (e.symm y.val) ^ n = 1
    rw [← hv, e.apply_symm_apply]
    exact y.property⟩
  invFun x := ⟨e x.val, (hv x.val).trans x.property⟩
  left_inv y := Subtype.ext (e.apply_symm_apply y.val)
  right_inv x := Subtype.ext (e.symm_apply_apply x.val)
  map_mul' x y := Subtype.ext (e.symm.map_mul x.val y.val)

end Kernels

variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k p] [Fact p.Prime]
variable (B : Over (Spec (.of k))) [GrpObj B] [IsCommMonObj B] [Smooth B.hom]

def verschiebungKernelPointsEquivTorsion :
    Quotient.Construction.kernelPoints (Verschiebung.Construction.verschiebung p k B) (Over.mk (𝟙 (Spec (.of k)))) ≃*
      (powMonoidHom p : (Over.mk (𝟙 (Spec (.of k))) ⟶ B) →* _).ker := by
  let h := Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)
  let e := relativeFrobeniusPointsEquiv p Fact.out h B (𝟙 _)
  apply powerFactorKernelEquiv e (IsMonHom.monoidHom (Verschiebung.Construction.verschiebung p k B) _) p
  intro x
  change (x ≫ Frobenius.Construction.relativeFrobenius p Fact.out h B) ≫ Verschiebung.Construction.verschiebung p k B = x ^ p
  rw [Category.assoc, Verschiebung.Construction.frobenius_comp_verschiebung, MonObj.comp_pow, Category.comp_id]

theorem verschiebungKernelPoints_card :
    Nat.card (Quotient.Construction.kernelPoints (Verschiebung.Construction.verschiebung p k B) (Over.mk (𝟙 (Spec (.of k))))) =
      Nat.card ((powMonoidHom p : (Over.mk (𝟙 (Spec (.of k))) ⟶ B) →* _).ker) :=
  Nat.card_congr (verschiebungKernelPointsEquivTorsion p k B).toEquiv

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusPoints
