import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.EtaleSubgroupStability

/-! # Stable Subgroup -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StableSubgroup.StableSubgroupParameter

noncomputable section

/-! Finitely many actual subgroup-stability conditions define a
constructed clopen parameter scheme. Its classification retains every
test scheme and gives a unique lift to the parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

variable {S : Scheme.{0}} {H T : Over S} [GrpObj H]
    [IsFinite H.hom] [Etale H.hom]
    {F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup H T} (R : F.Model)
    {I : Type*} [Finite I] (e : I → (H ⟶ H))

def locus : T.left.Opens :=
  ⟨⋂ i, (ReferenceFamily.Finite.EtaleSubgroupStability.finiteEtaleSubgroupStabilityLocus R (e i) : Set T.left),
    (isClopen_iInter_of_finite fun i =>
      ⟨ReferenceFamily.Finite.EtaleSubgroupStability.finiteEtaleSubgroupStabilityLocus_isClosed R (e i),
        (ReferenceFamily.Finite.EtaleSubgroupStability.finiteEtaleSubgroupStabilityLocus R (e i)).isOpen⟩).isOpen⟩

theorem locus_isClosed : IsClosed (locus R e : Set T.left) :=
  (isClopen_iInter_of_finite fun i =>
    ⟨ReferenceFamily.Finite.EtaleSubgroupStability.finiteEtaleSubgroupStabilityLocus_isClosed R (e i),
      (ReferenceFamily.Finite.EtaleSubgroupStability.finiteEtaleSubgroupStabilityLocus R (e i)).isOpen⟩).isClosed

def carrier : Over S := Over.mk ((locus R e).ι ≫ T.hom)

def inclusion : carrier R e ⟶ T := Over.homMk (locus R e).ι rfl

instance inclusion_open : IsOpenImmersion (inclusion R e).left :=
  inferInstanceAs (IsOpenImmersion (locus R e).ι)

instance inclusion_closed : IsClosedImmersion (inclusion R e).left := by
  apply IsClosedImmersion.of_isPreimmersion
  change IsClosed (Set.range (locus R e).ι)
  rw [Scheme.Opens.range_ι]
  exact locus_isClosed R e

instance inclusion_mono : Mono (inclusion R e) := Over.mono_of_mono_left _

instance carrier_finite [IsFinite T.hom] : IsFinite (carrier R e).hom :=
  inferInstanceAs (IsFinite ((inclusion R e).left ≫ T.hom))

instance carrier_etale [Etale T.hom] : Etale (carrier R e).hom :=
  inferInstanceAs (Etale ((inclusion R e).left ≫ T.hom))

theorem classifies {U : Over S} (f : U ⟶ T) :
    (∃! g : U ⟶ carrier R e, g ≫ inclusion R e = f) ↔
      ∀ i, SubgroupStability.RelativeSubgroupStable (F.baseChange f) (e i) := by
  have hc : Set.range f.left ⊆ locus R e ↔
      ∀ i, SubgroupStability.RelativeSubgroupStable (F.baseChange f) (e i) := by
    constructor
    · intro h i
      apply (ReferenceFamily.Finite.EtaleSubgroupStability.finiteEtaleSubgroupStabilityLocus_classifies R (e i) f).mp
      intro y hy
      exact Set.mem_iInter.mp (h hy) i
    · intro h y hy
      apply Set.mem_iInter.mpr
      intro i
      exact (ReferenceFamily.Finite.EtaleSubgroupStability.finiteEtaleSubgroupStabilityLocus_classifies R (e i) f).mpr (h i) hy
  refine Iff.trans ?_ hc
  constructor
  · rintro ⟨g, hg, _⟩ y ⟨x, rfl⟩
    rw [← hg]
    exact (g.left x).property
  · intro hr
    have hr' : Set.range f.left ⊆ Set.range (locus R e).ι := by
      rw [Scheme.Opens.range_ι]
      exact hr
    let l := IsOpenImmersion.lift (locus R e).ι f.left hr'
    have hl : l ≫ (locus R e).ι = f.left := IsOpenImmersion.lift_fac _ _ _
    let g : U ⟶ carrier R e := Over.homMk l (by
      change l ≫ ((locus R e).ι ≫ T.hom) = U.hom
      rw [← Category.assoc, hl, f.w])
    have hg : g ≫ inclusion R e = f := Over.OverMorphism.ext hl
    exact ⟨g, hg, fun a ha => (cancel_mono (inclusion R e)).mp (ha.trans hg.symm)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StableSubgroup.StableSubgroupParameter
