import OAI.AlgebraicGeometry.Picard.Homomorphisms.OrdinaryDivision

/-! # Unbundled Isogeny Count -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledIsogenyCount

noncomputable section

/-! Isogeny invariance of the geometric torsion count needs no chosen
relative dimension on either abelian scheme. Finiteness and surjectivity
on geometric points follow from the actual finite surjective morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A B : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
variable (f : A ⟶ B) [IsMonHom f] [IsFinite f.left] [Surjective f.left]

include f in
theorem isogeny_torsion_card_unbundled (n : ℕ)
    [Finite (powMonoidHom n : (Over.mk (𝟙 (Spec (.of k))) ⟶ A) →* _).ker] :
    Nat.card (powMonoidHom n : (Over.mk (𝟙 (Spec (.of k))) ⟶ A) →* _).ker =
      Nat.card (powMonoidHom n : (Over.mk (𝟙 (Spec (.of k))) ⟶ B) →* _).ker := by
  let q := IsMonHom.monoidHom f (Over.mk (𝟙 (Spec (.of k))))
  have : Finite {x : Spec (.of k) ⟶ A.left //
      x ≫ f.left = (1 : Over.mk (𝟙 (Spec (.of k))) ⟶ B).left} :=
    AbelianScheme.FrobeniusKernel.GeometricIsogeny.Construction.finite_geometric_lifts f.left _
  have : Finite q.ker := Finite.of_equiv _
    (AbelianScheme.FrobeniusKernel.GeometricIsogeny.Construction.overGeometricFiberEquiv f (𝟙 _) 1).symm
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := AbelianScheme.FrobeniusKernel.GeometricIsogeny.Construction.exists_geometric_lift f.left y.left
    let z := (AbelianScheme.FrobeniusKernel.GeometricIsogeny.Construction.overGeometricFiberEquiv f (𝟙 _) y).symm ⟨x, hx⟩
    exact ⟨z.val, z.property⟩
  apply AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion_card_eq_of_kernel_divisible q hq n
  intro x
  exact OrdinaryDivision.Construction.rational_points_divisible_of_finite_torsion A n x.val

include f in
theorem isogeny_preserves_ordinary_count_unbundled (p : ℕ) (hp : p.Prime) (g : ℕ)
    (hordinary : Nat.card (powMonoidHom p :
      (Over.mk (𝟙 (Spec (.of k))) ⟶ A) →* _).ker = p ^ g) :
    Nat.card (powMonoidHom p : (Over.mk (𝟙 (Spec (.of k))) ⟶ B) →* _).ker = p ^ g := by
  have : Finite (powMonoidHom p : (Over.mk (𝟙 (Spec (.of k))) ⟶ A) →* _).ker :=
    Nat.finite_of_card_ne_zero (hordinary ▸ pow_ne_zero g hp.ne_zero)
  exact (isogeny_torsion_card_unbundled f p).symm.trans hordinary

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledIsogenyCount
