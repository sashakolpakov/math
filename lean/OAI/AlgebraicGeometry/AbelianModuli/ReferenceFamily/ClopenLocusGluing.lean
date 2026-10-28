import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LocalLocusPointCriterion
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Clopen Locus Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ClopenLocusGluing

noncomputable section

/-! Compatible local clopen classifiers glue to the actual open
subscheme on every test scheme. The construction retains nilpotents. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem openImmersion_unique_lift_iff_range {X Z T : Scheme.{0}}
    (j : Z ⟶ X) [IsOpenImmersion j] (f : T ⟶ X) :
    (∃! q : T ⟶ Z, q ≫ j = f) ↔ Set.range f ⊆ Set.range j := by
  constructor
  · rintro ⟨q, hq, _⟩ _ ⟨t, rfl⟩
    exact ⟨q t, congrArg (fun m : T ⟶ X => m t) hq⟩
  · intro h
    let q := IsOpenImmersion.lift j f h
    have hq : q ≫ j = f := IsOpenImmersion.lift_fac j f h
    exact ⟨q, hq, fun v hv => (cancel_mono j).mp (hv.trans hq.symm)⟩

theorem exists_global_clopen_locus_of_local_classifiers
    {S : Scheme.{0}} (F : Subfunctor (yoneda.obj S))
    {I : Type} (U : I → S.Opens) (hU : IsOpenCover U)
    (Z : I → Scheme.{0}) (j : ∀ i, Z i ⟶ (U i).toScheme)
    (hj : ∀ i, IsOpenImmersion (j i)) (hcj : ∀ i, IsClosedImmersion (j i))
    (hclass : ∀ (i : I) (T : Scheme.{0}) (x : T ⟶ (U i).toScheme),
      x ≫ (U i).ι ∈ F.obj (.op T) ↔ ∃! q : T ⟶ Z i, q ≫ j i = x)
    (hgeo : ∀ (T : Scheme.{0}) (x : T ⟶ S),
      (∀ (k : Type) [Field k] [IsAlgClosed k] (p : Spec (.of k) ⟶ T),
        p ≫ x ∈ F.obj (.op (Spec (.of k)))) → x ∈ F.obj (.op T)) :
    ∃ L : S.Opens, IsClosed (L : Set S) ∧
      ∀ (T : Scheme.{0}) (x : T ⟶ S),
        x ∈ F.obj (.op T) ↔ ∃! q : T ⟶ L.toScheme, q ≫ L.ι = x := by
  let hc : ∀ (i : I) (T : Scheme.{0}) [IsReduced T] (x : T ⟶ (U i).toScheme),
      x ≫ (U i).ι ∈ F.obj (.op T) ↔ Set.range x ⊆ Set.range (j i) := by
    intro i T _ x
    let := hj i
    exact (hclass i T x).trans (openImmersion_unique_lift_iff_range (j i) x)
  let W := PELModuli.IntegralModel.LocalLocusPointCriterion.ReducedLocusGluing.locusSet U Z j
  have hopen : IsOpen W := by
    apply hU.isOpen_iff_coe_preimage.mpr
    intro i
    change IsOpen ((U i).ι ⁻¹' W)
    rw [PELModuli.IntegralModel.LocalLocusPointCriterion.ReducedLocusGluing.locusSet_preimage F U hU Z j hc i]
    let := hj i
    exact (j i).isOpenEmbedding.isOpen_range
  have hclosed : IsClosed W := by
    apply hU.isClosed_iff_coe_preimage.mpr
    intro i
    change IsClosed ((U i).ι ⁻¹' W)
    rw [PELModuli.IntegralModel.LocalLocusPointCriterion.ReducedLocusGluing.locusSet_preimage F U hU Z j hc i]
    let := hcj i
    exact (j i).isClosedEmbedding.isClosed_range
  let L : S.Opens := ⟨W, hopen⟩
  refine ⟨L, hclosed, ?_⟩
  intro T x
  rw [openImmersion_unique_lift_iff_range, Scheme.Opens.range_ι]
  constructor
  · rintro hx _ ⟨t, rfl⟩
    let k := AlgebraicClosure (T.residueField t)
    let p : Spec (.of k) ⟶ T :=
      Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) k)) ≫ T.fromSpecResidueField t
    have hp : p (IsLocalRing.closedPoint k) = t := T.fromSpecResidueField_apply t _
    have hm : p ≫ x ∈ F.obj (.op (Spec (.of k))) := F.map p.op hx
    have hr := (PELModuli.IntegralModel.LocalLocusPointCriterion.ReducedLocusGluing.field_mem_iff_locusSet F U hU Z j hc (p ≫ x)).mp hm
    change x (p (IsLocalRing.closedPoint k)) ∈ W at hr
    exact hp ▸ hr
  · intro hx
    apply hgeo T x
    intro k hk ha p
    apply (PELModuli.IntegralModel.LocalLocusPointCriterion.ReducedLocusGluing.field_mem_iff_locusSet F U hU Z j hc (p ≫ x)).mpr
    exact hx ⟨p (IsLocalRing.closedPoint k), rfl⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ClopenLocusGluing
