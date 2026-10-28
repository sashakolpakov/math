import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldPointOpenLift
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.GeometricLocus
import Mathlib.Topology.LocalAtTarget

/-! # Local Locus Point Criterion -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LocalLocusPointCriterion.ReducedLocusGluing

noncomputable section

section

/-! Constructed local reduced classifiers determine a single underlying
subset. Field-valued tests detect this subset before any global scheme
or global representability property is chosen. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {S : Scheme.{0}} (F : Subfunctor (yoneda.obj S))
  {I : Type} (U : I → S.Opens) (hU : IsOpenCover U)
  (Z : I → Scheme.{0}) (j : ∀ i, Z i ⟶ (U i).toScheme)
  (hclass : ∀ (i : I) (T : Scheme.{0}) [IsReduced T] (x : T ⟶ (U i).toScheme),
    x ≫ (U i).ι ∈ F.obj (.op T) ↔ Set.range x ⊆ Set.range (j i))

def locusSet : Set S := ⋃ i, Set.range (j i ≫ (U i).ι)

include hU hclass in
theorem field_mem_iff_locusSet {k : Type} [Field k] (q : Spec (.of k) ⟶ S) :
    q ∈ F.obj (.op (Spec (.of k))) ↔ q (IsLocalRing.closedPoint k) ∈ locusSet U Z j := by
  constructor
  · intro hq
    obtain ⟨i, hi⟩ := hU.exists_mem (q (IsLocalRing.closedPoint k))
    obtain ⟨v, hv⟩ := FieldPointOpenLift.exists_field_point_open_lift (U i) q hi
    have hvF : v ≫ (U i).ι ∈ F.obj (.op (Spec (.of k))) := hv.symm ▸ hq
    obtain ⟨z, hz⟩ := (hclass i _ v).mp hvF ⟨IsLocalRing.closedPoint k, rfl⟩
    refine Set.mem_iUnion.mpr ⟨i, z, ?_⟩
    exact (congrArg (U i).ι hz).trans (congrArg (fun f => f (IsLocalRing.closedPoint k)) hv)
  · intro hq
    obtain ⟨i, z, hz⟩ := Set.mem_iUnion.mp hq
    have hi : q (IsLocalRing.closedPoint k) ∈ U i := by
      exact hz ▸ ((j i) z).property
    obtain ⟨v, hv⟩ := FieldPointOpenLift.exists_field_point_open_lift (U i) q hi
    have hvRange : Set.range v ⊆ Set.range (j i) := by
      rintro _ ⟨x, rfl⟩
      refine ⟨z, ?_⟩
      apply (U i).ι.isOpenEmbedding.injective
      exact hz.trans ((congrArg (fun f => f (IsLocalRing.closedPoint k)) hv).symm.trans
        (congrArg (fun y => (U i).ι (v y)) (Subsingleton.elim _ _)))
    exact hv ▸ (hclass i _ v).mpr hvRange

end

/-! The images of the constructed local classifiers agree on overlaps.
Their union is locally closed, and geometric detection determines its
classification property on every reduced test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {S : Scheme.{0}} (F : Subfunctor (yoneda.obj S))
  {I : Type} (U : I → S.Opens) (hU : IsOpenCover U)
  (Z : I → Scheme.{0}) (j : ∀ i, Z i ⟶ (U i).toScheme)
  (hclass : ∀ (i : I) (T : Scheme.{0}) [IsReduced T] (x : T ⟶ (U i).toScheme),
    x ≫ (U i).ι ∈ F.obj (.op T) ↔ Set.range x ⊆ Set.range (j i))

include hU hclass in
theorem locusSet_preimage (i : I) :
    (U i).ι ⁻¹' locusSet U Z j = Set.range (j i) := by
  ext x
  constructor
  · intro hx
    let k := AlgebraicClosure ((U i).toScheme.residueField x)
    let q : Spec (.of k) ⟶ (U i).toScheme :=
      Spec.map (CommRingCat.ofHom (algebraMap ((U i).toScheme.residueField x) k)) ≫
        (U i).toScheme.fromSpecResidueField x
    have hq : q (IsLocalRing.closedPoint k) = x :=
      (U i).toScheme.fromSpecResidueField_apply x _
    have hm : q ≫ (U i).ι ∈ F.obj (.op (Spec (.of k))) :=
      (field_mem_iff_locusSet F U hU Z j hclass (q ≫ (U i).ι)).mpr
        (by change (U i).ι (q (IsLocalRing.closedPoint k)) ∈ _; exact hq.symm ▸ hx)
    exact (hclass i _ q).mp hm ⟨IsLocalRing.closedPoint k, hq⟩
  · rintro ⟨z, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i, z, rfl⟩

include hU hclass in
theorem locusSet_locallyClosed (hj : ∀ i, IsImmersion (j i)) :
    IsLocallyClosed (locusSet U Z j) := by
  apply hU.isLocallyClosed_iff_coe_preimage.mpr
  intro i
  change IsLocallyClosed ((U i).ι ⁻¹' locusSet U Z j)
  rw [locusSet_preimage F U hU Z j hclass i]
  let := hj i
  exact IsImmersion.isLocallyClosed_range (f := j i)

include hU hclass in
theorem mem_iff_range_locusSet
    (hgeo : ∀ (T : Scheme.{0}) [IsReduced T] (x : T ⟶ S),
      (∀ (k : Type) [Field k] [IsAlgClosed k] (p : Spec (.of k) ⟶ T),
        p ≫ x ∈ F.obj (.op (Spec (.of k)))) → x ∈ F.obj (.op T))
    (T : Scheme.{0}) [IsReduced T] (x : T ⟶ S) :
    x ∈ F.obj (.op T) ↔ Set.range x ⊆ locusSet U Z j := by
  constructor
  · intro hx y hy
    obtain ⟨t, rfl⟩ := hy
    let k := AlgebraicClosure (T.residueField t)
    let p : Spec (.of k) ⟶ T :=
      Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) k)) ≫ T.fromSpecResidueField t
    have hp : p (IsLocalRing.closedPoint k) = t := T.fromSpecResidueField_apply t _
    have hm : p ≫ x ∈ F.obj (.op (Spec (.of k))) := F.map p.op hx
    have hr := (field_mem_iff_locusSet F U hU Z j hclass (p ≫ x)).mp hm
    change x (p (IsLocalRing.closedPoint k)) ∈ locusSet U Z j at hr
    exact hp ▸ hr
  · intro hx
    apply hgeo T x
    intro k hk ha p
    apply (field_mem_iff_locusSet F U hU Z j hclass (p ≫ x)).mpr
    exact hx ⟨p (IsLocalRing.closedPoint k), rfl⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LocalLocusPointCriterion.ReducedLocusGluing
