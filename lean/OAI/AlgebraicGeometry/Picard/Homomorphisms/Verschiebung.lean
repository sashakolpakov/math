import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelTorsion
import OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupDescent

/-! # Verschiebung -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.Verschiebung

noncomputable section

/-! Verschiebung is constructed by descent of multiplication by p through
the actual relative Frobenius quotient, over a perfect field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
variable (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A] [Smooth A.hom]

theorem exists_unique_verschiebung :
    ∃! V : Frobenius.Construction.frobeniusTwist p Fact.out (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) A ⟶ A,
      IsMonHom V ∧
      Frobenius.Construction.relativeFrobenius p Fact.out (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) A ≫ V =
        (𝟙 A) ^ p := by
  let hS := Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)
  let F := Frobenius.Construction.relativeFrobenius p Fact.out hS A
  have : Flat F.left := Homomorphisms.Smooth.Construction.relativeFrobenius_smooth_flat p Fact.out hS A
  have : IsMonHom ((𝟙 A) ^ p) := GroupDescent.Construction.groupHom_pow_isMonHom (𝟙 A) p
  apply GroupDescent.Construction.exists_unique_groupDescent_of_fpqc F ((𝟙 A) ^ p)
  rw [MonObj.comp_pow, Category.comp_id]
  exact KernelTorsion.Construction.relativeFrobenius_kernelInclusion_killed p k A

/-- The unique descended multiplication map. -/
def verschiebung :
    Frobenius.Construction.frobeniusTwist p Fact.out (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) A ⟶ A :=
  (exists_unique_verschiebung p k A).exists.choose

instance verschiebung_isMonHom : IsMonHom (verschiebung p k A) :=
  (exists_unique_verschiebung p k A).exists.choose_spec.1

theorem frobenius_comp_verschiebung :
    Frobenius.Construction.relativeFrobenius p Fact.out (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) A ≫
      verschiebung p k A = (𝟙 A) ^ p :=
  (exists_unique_verschiebung p k A).exists.choose_spec.2

theorem verschiebung_comp_frobenius :
    verschiebung p k A ≫
      Frobenius.Construction.relativeFrobenius p Fact.out (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) A =
        (𝟙 (Frobenius.Construction.frobeniusTwist p Fact.out
          (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) A)) ^ p := by
  let F := Frobenius.Construction.relativeFrobenius p Fact.out
    (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) A
  have : Flat F.left := Homomorphisms.Smooth.Construction.relativeFrobenius_smooth_flat p Fact.out _ A
  have : EffectiveEpi F := GroupDescent.Construction.effectiveEpi_over_of_fpqc F
  apply (cancel_epi F).mp
  rw [← Category.assoc, frobenius_comp_verschiebung, MonObj.pow_comp,
    Category.id_comp, MonObj.comp_pow, Category.comp_id]

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.Verschiebung
