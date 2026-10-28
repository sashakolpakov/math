import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.SubgroupChoices
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.RepresentabilityAnd

/-! # Torsion Choices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.TorsionChoices.Construction

noncomputable section

/-!
The original TorsionQuotient subgroup-choice functor, evaluated at a geometric point,
classifies the actual subgroups of torsion points of the stated type.
The resulting subgroup is explicitly the restriction of the original
relative subgroup, rather than a new unlabeled group with the same size.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
  (n : ℕ) (M : Type u) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
  [IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom] [Etale (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom]
  (K : Type u) [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ S)

local instance : Fintype (Multiplicative M) := Fintype.ofFinite _

def geometricTorsionChoiceEquiv :
    TorsionQuotient.SubgroupFunctor.SubgroupChoice A n M (Over.mk b) ≃
      {J : Subgroup (Over.mk b ⟶ TorsionQuotient.SubgroupFunctor.torsionScheme A n) // Nonempty (J ≃* Multiplicative M)} :=
  (TorsionQuotient.RepresentabilityAnd.Representability.representable A n M).homEquiv.symm.trans
    (SubgroupChoices.Construction.geometricSubgroupPointEquiv (TorsionQuotient.RepresentabilityAnd.Representability.data A n M) K b)

theorem geometricTorsionChoiceEquiv_points (F : TorsionQuotient.SubgroupFunctor.SubgroupChoice A n M (Over.mk b)) :
    (geometricTorsionChoiceEquiv A n M K b F).val =
      (TorsionQuotient.Subgroups.TorsionSubgroups.restrict A n F.subgroup).points (Over.mk b) (𝟙 _) := by
  obtain ⟨p, rfl⟩ := TorsionQuotient.RepresentabilityAnd.Representability.points_surjective A n M (Over.mk b) F
  change (SubgroupChoices.Construction.geometricSubgroupPoint (TorsionQuotient.RepresentabilityAnd.Representability.data A n M) K b
    ((TorsionQuotient.RepresentabilityAnd.Representability.representable A n M).homEquiv.symm
      ((TorsionQuotient.RepresentabilityAnd.Representability.representable A n M).homEquiv p))).val = _
  rw [Equiv.symm_apply_apply]
  ext a
  change a ∈ (TorsionQuotient.UniversalSubgroupEq.UniversalSubgroup.subgroup (TorsionQuotient.RepresentabilityAnd.Representability.data A n M)).points (Over.mk b) p ↔
    ∃ x, x ∈ (TorsionQuotient.UniversalSubgroupEq.UniversalSubgroup.subgroup (TorsionQuotient.RepresentabilityAnd.Representability.data A n M)).points
      (Over.mk b) ((𝟙 _) ≫ p) ∧ x ≫ TorsionQuotient.SubgroupFunctor.torsionι A n = a ≫ TorsionQuotient.SubgroupFunctor.torsionι A n
  rw [Category.id_comp]
  constructor
  · intro ha
    exact ⟨a, ha, rfl⟩
  · rintro ⟨x, hx, he⟩
    have hxa := (cancel_mono (TorsionQuotient.SubgroupFunctor.torsionι A n)).mp he
    rwa [hxa] at hx

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.TorsionChoices.Construction
