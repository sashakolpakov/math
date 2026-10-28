import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteGroupMaps
import OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupRigidity
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteEndomorphism

/-! # Ordinary Division -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.OrdinaryDivision

noncomputable section

/-! Finite geometric torsion implies division of rational points on an
abelian variety. In particular the ordinary p-rank hypothesis supplies
the division needed for isogeny invariance of p-rank. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

attribute [local instance] GroupDescent.Construction.groupHom_pow_isMonHom

def torsionKernelPointEquiv {S : Scheme.{u}}
    (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) (T : Over S) :
    (T ⟶ Kernel.Construction.kernelScheme ((𝟙 A) ^ n)) ≃ (powMonoidHom n : (T ⟶ A) →* _).ker :=
  (FiniteGroupMaps.Construction.kernelPointEquiv ((𝟙 A) ^ n) T).trans
    (Equiv.subtypeEquivRight fun x => by
      change x ≫ (𝟙 A) ^ n = 1 ↔ x ^ n = 1
      rw [MonObj.comp_pow, Category.comp_id])

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
variable (n : ℕ)
variable [Finite (powMonoidHom n : (Over.mk (𝟙 (Spec (.of k))) ⟶ A) →* _).ker]

omit [Smooth A.hom] [GeometricallyConnected A.hom] in
theorem multiplication_finite_of_finite_rational_torsion : IsFinite ((𝟙 A) ^ n).left := by
  have : Finite (Over.mk (𝟙 (Spec (.of k))) ⟶ Kernel.Construction.kernelScheme ((𝟙 A) ^ n)) :=
    Finite.of_equiv _ (torsionKernelPointEquiv A n _).symm
  have : IsFinite (Kernel.Construction.kernelScheme ((𝟙 A) ^ n)).hom :=
    FiniteGeometricPoints.Construction.finite_morphism_of_proper_finite_rationalPoints (Kernel.Construction.kernelScheme ((𝟙 A) ^ n))
  exact FiniteGroupMaps.Construction.groupHom_finite_of_finite_kernel ((𝟙 A) ^ n)

theorem multiplication_surjective_of_finite_rational_torsion :
    Surjective ((𝟙 A) ^ n).left := by
  have : IsFinite ((𝟙 A) ^ n).left := multiplication_finite_of_finite_rational_torsion A n
  have : IsIntegral A.left := GroupRigidity.Construction.integral_smooth_proper_connected_group A
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : IsNoetherian A.left := ⟨⟩
  exact ArithmeticGeometry.OrdinaryLocus.Openness.FiniteEndomorphism.Construction.surjective_finite_endomorphism_of_isIntegral ((𝟙 A) ^ n).left

theorem rational_points_divisible_of_finite_torsion :
    Function.Surjective (fun x : Over.mk (𝟙 (Spec (.of k))) ⟶ A => x ^ n) := by
  let f : A ⟶ A := (𝟙 A) ^ n
  have : IsFinite f.left := multiplication_finite_of_finite_rational_torsion A n
  have : Surjective f.left := multiplication_surjective_of_finite_rational_torsion A n
  intro y
  obtain ⟨x, hx⟩ := AbelianScheme.FrobeniusKernel.GeometricIsogeny.Construction.exists_geometric_lift f.left y.left
  let z := (AbelianScheme.FrobeniusKernel.GeometricIsogeny.Construction.overGeometricFiberEquiv f (𝟙 _) y).symm ⟨x, hx⟩
  refine ⟨z.val, ?_⟩
  have h := z.property
  simpa only [f, MonObj.comp_pow, Category.comp_id] using h

theorem isogeny_torsion_card_of_finite_source {g h : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k)))
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (n : ℕ)
    [Finite (A.torsionPoints n (Over.mk (𝟙 (Spec (.of k)))))] :
    Nat.card (A.torsionPoints n (Over.mk (𝟙 (Spec (.of k))))) =
      Nat.card (B.torsionPoints n (Over.mk (𝟙 (Spec (.of k))))) := by
  have : Finite (powMonoidHom n : (Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme) →* _).ker :=
    inferInstanceAs (Finite (A.torsionPoints n (Over.mk (𝟙 (Spec (.of k))))))
  apply AbelianScheme.FrobeniusKernel.GeometricIsogeny.Construction.isogeny_geometric_qRank_preserved f (𝟙 _) n
  intro x
  exact rational_points_divisible_of_finite_torsion A.scheme n x.val

theorem isogeny_preserves_ordinary_torsion_count {g : ℕ}
    (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (p : ℕ) (hp : p.Prime)
    (hordinary : Nat.card (A.torsionPoints p (Over.mk (𝟙 (Spec (.of k))))) = p ^ g) :
    Nat.card (B.torsionPoints p (Over.mk (𝟙 (Spec (.of k))))) = p ^ g := by
  have : Finite (A.torsionPoints p (Over.mk (𝟙 (Spec (.of k))))) :=
    Nat.finite_of_card_ne_zero (hordinary ▸ pow_ne_zero g hp.ne_zero)
  exact (isogeny_torsion_card_of_finite_source A B f p).symm.trans hordinary

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.OrdinaryDivision
