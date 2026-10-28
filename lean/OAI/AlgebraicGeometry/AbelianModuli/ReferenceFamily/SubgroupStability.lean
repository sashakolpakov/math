import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

/-! # Subgroup Stability -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SubgroupStability

noncomputable section

/-! Stability of a represented subgroup is equivalent to stability of
its actual universal section, with all test schemes retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

universe u

variable {S : Scheme.{u}} {H T : Over S} [GrpObj H]

def RelativeSubgroupStable (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup H T) (e : H ⟶ H) : Prop :=
  ∀ (X : Over S) (t : X ⟶ T) (a : X ⟶ H),
    a ∈ F.points X t → a ≫ e ∈ F.points X t

theorem relativeSubgroupStable_baseChange {F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup H T}
    {U : Over S} (e : H ⟶ H) (h : RelativeSubgroupStable F e) (f : U ⟶ T) :
    RelativeSubgroupStable (F.baseChange f) e :=
  fun X t a ha => h X (t ≫ f) a ha

theorem relativeSubgroupStable_iff_model {F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup H T}
    (R : F.Model) (e : H ⟶ H) :
    RelativeSubgroupStable F e ↔ R.toGroup ≫ e ∈ F.points R.carrier R.toBase := by
  constructor
  · intro h
    apply h R.carrier R.toBase R.toGroup
    exact (R.points_iff _ _ _).mpr
      ⟨𝟙 R.carrier, Category.id_comp _, Category.id_comp _⟩
  · intro he X t a ha
    obtain ⟨h, hb, hg⟩ := (R.points_iff X t a).mp ha
    have hm := F.naturality h R.toBase he
    rw [← Category.assoc, hg, hb] at hm
    exact hm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SubgroupStability
