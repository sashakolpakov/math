import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeometricTorsionRank
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleGeometricCardinality
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrimeTorsionLabels
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.TorsionDivision
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.Splitting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupIsomorphisms

/-! # Geometric Prime Level -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeometricPrimeLevel

noncomputable section

/-! Actual full ordered prime levels on geometric abelian schemes in
every characteristic where the prime is invertible. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

variable {K : Type} [Field K] [IsAlgClosed K] {g : ℕ}

def fieldConstantValuesEquiv (G : Type) [Group G] : G ≃* LocallyConstant (Spec (.of K)) G where
  toFun := LocallyConstant.const _
  invFun f := f default
  left_inv _ := rfl
  right_inv f := by
    apply LocallyConstant.ext
    intro x
    exact congrArg f (Subsingleton.elim default x)
  map_mul' _ _ := rfl

theorem fullLevel_of_prime_torsion_card (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K)))
    (p : ℕ) [Fact p.Prime] [IsFinite (A.torsionScheme p).hom] [Etale (A.torsionScheme p).hom]
    (hc : Nat.card (A.torsionPoints p (Over.mk (𝟙 (Spec (.of K))))) = p ^ (2 * g)) :
    Nonempty (A.FullLevel p) := by
  obtain ⟨G, hG, hfin, ⟨e⟩⟩ := AbelianModuli.ReferenceFamily.Geometric.Splitting.GeometricSplitting.exists_constant_groupIso (A.torsionScheme p)
  let _ : Group G := hG
  let _ : Finite G := hfin
  let e' : AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor (Spec (.of K)) G ≅ A.torsionFunctor p :=
    e ≪≫ A.torsionSchemeYonedaIso p
  let ep : G ≃* A.torsionPoints p (Over.mk (𝟙 (Spec (.of K)))) :=
    (fieldConstantValuesEquiv (K := K) G).trans
      ((e'.app (op (Over.mk (𝟙 (Spec (.of K)))))).groupIsoToMulEquiv)
  obtain ⟨ec⟩ := PrimeTorsionLabels.prime_torsion_label_equiv p (2 * g)
    (A.torsionPoints p (Over.mk (𝟙 (Spec (.of K))))) (fun x => by
      apply Subtype.ext
      exact x.property) hc
  exact ⟨AbelianModuli.HilbertConstruction.Constant.GroupIsomorphisms.constantGroupIsoOfLabels (LocallyConstant.const (Spec (.of K)) (ec.trans ep.symm)) ≪≫ e'⟩

theorem geometric_exists_prime_fullLevel (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K)))
    (p : ℕ) [Fact p.Prime]
    (hp : ∀ x : Spec (.of K), IsUnit (p : (Spec (.of K)).presheaf.stalk x)) :
    Nonempty (A.FullLevel p) := by
  obtain ⟨hf, he⟩ := TorsionDivision.torsionScheme_finite_etale A p hp
  let _ : IsFinite (A.torsionScheme p).hom := hf
  let _ : Etale (A.torsionScheme p).hom := he
  apply fullLevel_of_prime_torsion_card A p
  exact (Nat.card_congr (A.torsionSchemePointsEquiv p (Over.mk (𝟙 (Spec (.of K)))))).symm.trans
    ((IntegralModel.Finite.EtaleGeometricCardinality.finiteEtale_geometric_point_card (A.torsionScheme p) default).trans
      (GeometricTorsionRank.geometric_torsion_finrank A p (Fact.out : p.Prime).pos default))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeometricPrimeLevel
