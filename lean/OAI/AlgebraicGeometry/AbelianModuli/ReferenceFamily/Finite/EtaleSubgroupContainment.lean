import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProperMapImmersionLocus
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.EtaleSubgroup

/-! # Etale Subgroup Containment -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.EtaleSubgroupContainment

/-! Containment of two actual finite etale subgroup families is a
clopen condition on their common parameter. The classifier retains
all test schemes, including nonreduced ones. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

variable {S : Scheme.{0}} {H T : Over S} [GrpObj H]

def RelativeSubgroupContained (F G : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup H T) : Prop :=
  ∀ (X : Over S) (t : X ⟶ T), F.points X t ≤ G.points X t

theorem relativeSubgroupContained_baseChange {F G : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup H T}
    (h : RelativeSubgroupContained F G) {U : Over S} (f : U ⟶ T) :
    RelativeSubgroupContained (F.baseChange f) (G.baseChange f) :=
  fun X t => h X (t ≫ f)

theorem relativeSubgroupContained_iff_model {F G : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup H T}
    (R : F.Model) :
    RelativeSubgroupContained F G ↔ R.toGroup ∈ G.points R.carrier R.toBase := by
  constructor
  · intro h
    exact h R.carrier R.toBase ((R.points_iff _ _ _).mpr
      ⟨𝟙 R.carrier, Category.id_comp _, Category.id_comp _⟩)
  · intro h X t a ha
    obtain ⟨k, hk, ha'⟩ := (R.points_iff X t a).mp ha
    have hm := G.naturality k R.toBase h
    rwa [hk, ha'] at hm

theorem relativeSubgroup_eq_iff_contained (F G : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup H T) :
    F = G ↔ RelativeSubgroupContained F G ∧ RelativeSubgroupContained G F := by
  constructor
  · rintro rfl
    exact ⟨fun _ _ => le_rfl, fun _ _ => le_rfl⟩
  · rintro ⟨hFG, hGF⟩
    ext X t
    exact le_antisymm (hFG X t) (hGF X t)

variable [IsFinite H.hom] [Etale H.hom]
    {F G : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup H T} (R : F.Model) (Q : G.Model)

def finiteEtaleSubgroupContainmentLocus : T.left.Opens := by
  let : IsFinite R.toBase.left := R.finite
  exact ProperMapImmersionLocus.properMapImmersionLocus R.toBase.left
    (AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.inclusion R).left (AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.inclusion Q).left

theorem finiteEtaleSubgroupContainmentLocus_isClosed :
    IsClosed (finiteEtaleSubgroupContainmentLocus R Q : Set T.left) := by
  let : IsFinite R.toBase.left := R.finite
  let : Etale R.toBase.left := AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.etale R
  exact ProperMapImmersionLocus.properMapImmersionLocus_isClosed R.toBase.left
    (AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.inclusion R).left (AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.inclusion Q).left
    R.toBase.left.isOpenMap

theorem finiteEtaleSubgroupContainmentLocus_classifies
    {U : Over S} (f : U ⟶ T) :
    Set.range f.left ⊆ finiteEtaleSubgroupContainmentLocus R Q ↔
      RelativeSubgroupContained (F.baseChange f) (G.baseChange f) := by
  let : IsFinite R.toBase.left := R.finite
  let a : (R.baseChange f).carrier ⟶ R.carrier := pullback.fst R.toBase f
  let b : (R.baseChange f).carrier ⟶ U := pullback.snd R.toBase f
  let v : R.carrier ⟶ T ⊗ H := AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.inclusion R
  have hs : IsPullback a.left b.left R.toBase.left f.left :=
    (IsPullback.of_hasPullback R.toBase f).map (Over.forget S)
  have ht : Set.range f.left ⊆ finiteEtaleSubgroupContainmentLocus R Q ↔
      ∀ z : (R.baseChange f).carrier.left,
        v.left (a.left z) ∈ Set.range (AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.inclusion Q).left :=
    ProperMapImmersionLocus.schemeFiberwiseOpenLocus_baseChange R.toBase.left
      (v.left ⁻¹ᵁ ⟨Set.range (AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.inclusion Q).left,
        (AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.inclusion Q).left.isOpenMap.isOpen_range⟩)
      a.left b.left f.left hs
  refine ht.trans ?_
  rw [relativeSubgroupContained_iff_model (R.baseChange f)]
  change (∀ z : (R.baseChange f).carrier.left,
      v.left (a.left z) ∈ Set.range (AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.inclusion Q).left) ↔
    a ≫ R.toGroup ∈ G.points (R.baseChange f).carrier (b ≫ f)
  rw [AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.membership_iff_range Q (b ≫ f) (a ≫ R.toGroup)]
  have hp : lift (b ≫ f) (a ≫ R.toGroup) = a ≫ v := by
    rw [← show a ≫ R.toBase = b ≫ f from pullback.condition]
    exact (comp_lift a R.toBase R.toGroup).symm
  rw [hp]
  constructor
  · intro h y hy
    obtain ⟨z, rfl⟩ := hy
    exact h z
  · intro h z
    exact h ⟨z, rfl⟩

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.EtaleSubgroupContainment

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.EtaleSubgroupContainment.FiniteEtaleSubgroupEquality

/-! Equality of two finite etale subgroup families is represented by
an actual clopen subscheme of their parameter, with unique classifiers
on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

variable {S : Scheme.{0}} {H T : Over S} [GrpObj H]
    [IsFinite H.hom] [Etale H.hom]
    {F G : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup H T} (R : F.Model) (Q : G.Model)

def locus : T.left.Opens :=
  finiteEtaleSubgroupContainmentLocus R Q ⊓ finiteEtaleSubgroupContainmentLocus Q R

theorem locus_isClosed : IsClosed (locus R Q : Set T.left) :=
  (finiteEtaleSubgroupContainmentLocus_isClosed R Q).inter
    (finiteEtaleSubgroupContainmentLocus_isClosed Q R)

theorem range_subset_locus_iff {U : Over S} (f : U ⟶ T) :
    Set.range f.left ⊆ locus R Q ↔ F.baseChange f = G.baseChange f := by
  change (Set.range f.left ⊆
    (finiteEtaleSubgroupContainmentLocus R Q : Set T.left) ∩
      (finiteEtaleSubgroupContainmentLocus Q R : Set T.left)) ↔ _
  rw [Set.subset_inter_iff, finiteEtaleSubgroupContainmentLocus_classifies R Q f,
    finiteEtaleSubgroupContainmentLocus_classifies Q R f]
  exact (relativeSubgroup_eq_iff_contained _ _).symm

def carrier : Over S := Over.mk ((locus R Q).ι ≫ T.hom)

def inclusion : FiniteEtaleSubgroupEquality.carrier R Q ⟶ T := Over.homMk (locus R Q).ι rfl

instance inclusion_open : IsOpenImmersion (inclusion R Q).left :=
  inferInstanceAs (IsOpenImmersion (locus R Q).ι)

instance inclusion_closed : IsClosedImmersion (inclusion R Q).left := by
  apply IsClosedImmersion.of_isPreimmersion
  change IsClosed (Set.range (locus R Q).ι)
  rw [Scheme.Opens.range_ι]
  exact locus_isClosed R Q

instance inclusion_mono : Mono (inclusion R Q) := Over.mono_of_mono_left _

instance carrier_finite [IsFinite T.hom] : IsFinite (FiniteEtaleSubgroupEquality.carrier R Q).hom :=
  inferInstanceAs (IsFinite ((inclusion R Q).left ≫ T.hom))

instance carrier_etale [Etale T.hom] : Etale (FiniteEtaleSubgroupEquality.carrier R Q).hom :=
  inferInstanceAs (Etale ((inclusion R Q).left ≫ T.hom))

theorem classifies {U : Over S} (f : U ⟶ T) :
    (∃! g : U ⟶ FiniteEtaleSubgroupEquality.carrier R Q, g ≫ inclusion R Q = f) ↔
      F.baseChange f = G.baseChange f := by
  refine Iff.trans ?_ (range_subset_locus_iff R Q f)
  constructor
  · rintro ⟨g, hg, _⟩ y ⟨x, rfl⟩
    rw [← hg]
    exact (g.left x).property
  · intro hr
    have hr' : Set.range f.left ⊆ Set.range (locus R Q).ι := by
      rw [Scheme.Opens.range_ι]
      exact hr
    let l := IsOpenImmersion.lift (locus R Q).ι f.left hr'
    have hl : l ≫ (locus R Q).ι = f.left := IsOpenImmersion.lift_fac _ _ _
    let g : U ⟶ FiniteEtaleSubgroupEquality.carrier R Q := Over.homMk l (by
      change l ≫ ((locus R Q).ι ≫ T.hom) = U.hom
      rw [← Category.assoc, hl, f.w])
    have hg : g ≫ inclusion R Q = f := Over.OverMorphism.ext hl
    exact ⟨g, hg, fun a ha => (cancel_mono (inclusion R Q)).mp (ha.trans hg.symm)⟩

theorem universal_equality :
    F.baseChange (inclusion R Q) = G.baseChange (inclusion R Q) := by
  apply (classifies R Q (inclusion R Q)).mp
  exact ⟨𝟙 (FiniteEtaleSubgroupEquality.carrier R Q), Category.id_comp _,
    fun a ha => (cancel_mono (inclusion R Q)).mp (ha.trans (Category.id_comp _).symm)⟩

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.EtaleSubgroupContainment.FiniteEtaleSubgroupEquality

end

end OAI
