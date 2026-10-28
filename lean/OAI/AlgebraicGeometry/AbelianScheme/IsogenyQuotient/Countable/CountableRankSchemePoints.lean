import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.RankClosedPoints
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Countable Rank Scheme Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.CountableRankSchemePoints.Construction

noncomputable section

section

/-! Countable-rank rational-point detection on actual affine schemes.
Any map from such a coefficient spectrum lands in an open subset
containing all rational points of its target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (C R : Type) [Field C] [Uncountable C] [IsAlgClosed C] [CommRing R] [Algebra C R]

omit [Uncountable C] [IsAlgClosed C] in
theorem rationalKernelPoint_eq_specMap (f : R →ₐ[C] C) :
    RankClosedPoints.Construction.rationalKernelPoint C R f =
      Spec.map (CommRingCat.ofHom f.toRingHom) (IsLocalRing.closedPoint C) := by
  apply PrimeSpectrum.ext
  change RingHom.ker f.toRingHom = Ideal.comap f.toRingHom (IsLocalRing.maximalIdeal C)
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

omit [Uncountable C] [IsAlgClosed C] in
theorem rationalSchemePoint_base (f : R →ₐ[C] C) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap C R)) = 𝟙 (Spec (.of C)) := by
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap C R) ≫ CommRingCat.ofHom f.toRingHom = 𝟙 _ := by
    ext x
    exact f.commutes x
  rw [h, Spec.map_id]

theorem scheme_open_eq_top_of_countable_rank
    (h : Module.rank C R ≤ Cardinal.aleph0) (U : (Spec (.of R)).Opens)
    (hU : ∀ p : Spec (.of C) ⟶ Spec (.of R),
      p ≫ Spec.map (CommRingCat.ofHom (algebraMap C R)) = 𝟙 _ →
        p (IsLocalRing.closedPoint C) ∈ U) : U = ⊤ := by
  apply SetLike.coe_injective
  exact RankClosedPoints.Construction.open_set_eq_univ_of_rational_points C R h (U : Set (Spec (.of R))) U.isOpen (fun f => by
    rw [rationalKernelPoint_eq_specMap]
    exact hU (Spec.map (CommRingCat.ofHom f.toRingHom)) (rationalSchemePoint_base C R f))

set_option backward.isDefEq.respectTransparency false in
theorem countable_rank_map_range_in_open
    (h : Module.rank C R ≤ Cardinal.aleph0) (X : Over (Spec (.of C))) (U : X.left.Opens)
    (hU : ∀ p : Over.mk (𝟙 (Spec (.of C))) ⟶ X, p.left (IsLocalRing.closedPoint C) ∈ U)
    (f : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap C R))) ⟶ X) :
    ∀ z, f.left z ∈ U := by
  have ht : f.left ⁻¹ᵁ U = ⊤ := scheme_open_eq_top_of_countable_rank C R h _ (by
    intro p hp
    let q : Over.mk (𝟙 (Spec (.of C))) ⟶
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap C R))) := Over.homMk p hp
    exact hU (q ≫ f))
  intro z
  exact (congrArg (fun V : (Spec (.of R)).Opens => z ∈ V) ht).mpr trivial

end

/-! A point defined over a countable field lands in every open of a
scalar extension that contains all rational points over the uncountable
algebraically closed extension field. The coefficient spectrum has
countable vector-space rank, so rational points detect its closed sets. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable (K C F : Type) [Field K] [Field C] [Field F] [Algebra K C] [Algebra K F]
    (X : Over (Spec (.of K)))
    (b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ X)

def scalarExtensionFamilyMap :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap K C)))
      (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K C)))).obj X).left :=
  pullback.lift (pullback.snd _ _ ≫ b.left) (pullback.fst _ _) (by
    rw [Category.assoc, b.w]
    exact pullback.condition.symm)

set_option backward.isDefEq.respectTransparency false in
def scalarExtensionFamilyParameter :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[K] F)))) ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K C)))).obj X :=
  Over.homMk ((pullbackSpecIso K C F).inv ≫ scalarExtensionFamilyMap K C F X b) (by
    change ((pullbackSpecIso K C F).inv ≫ pullback.lift _ _ _) ≫ pullback.snd _ _ = _
    rw [Category.assoc, pullback.lift_snd]
    exact pullbackSpecIso_inv_fst' K C F)

set_option backward.isDefEq.respectTransparency false in
theorem countable_scalarExtension_family_range_in_open
    [Countable F] [Uncountable C] [IsAlgClosed C]
    (U : ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K C)))).obj X).left.Opens)
    (hU : ∀ p : Over.mk (𝟙 (Spec (.of C))) ⟶
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K C)))).obj X,
      p.left (IsLocalRing.closedPoint C) ∈ U) :
    ∀ y, scalarExtensionFamilyMap K C F X b y ∈ U := by
  have h := countable_rank_map_range_in_open C (C ⊗[K] F)
    (RankPoints.Construction.scalarExtension_rank_countable K C F) _ U hU (scalarExtensionFamilyParameter K C F X b)
  intro y
  have hy := h ((pullbackSpecIso K C F).hom y)
  have he : (pullbackSpecIso K C F).hom ≫ (scalarExtensionFamilyParameter K C F X b).left =
      scalarExtensionFamilyMap K C F X b := by
    change (pullbackSpecIso K C F).hom ≫ ((pullbackSpecIso K C F).inv ≫ _) = _
    rw [Iso.hom_inv_id_assoc]
  exact (congrArg (fun f => f y ∈ U) he).mp hy

set_option backward.isDefEq.respectTransparency false in
theorem countable_field_model_point_mem_open
    [Countable F] [Uncountable C] [IsAlgClosed C]
    (U : ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K C)))).obj X).left.Opens)
    (hU : ∀ p : Over.mk (𝟙 (Spec (.of C))) ⟶
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K C)))).obj X,
      p.left (IsLocalRing.closedPoint C) ∈ U)
    {L : Type} [Field L]
    (p : Spec (.of L) ⟶ ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K C)))).obj X).left)
    (t : Spec (.of L) ⟶ Spec (.of F))
    (ht : t ≫ b.left = p ≫ pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap K C)))) :
    p (IsLocalRing.closedPoint L) ∈ U := by
  let v := p ≫ pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap K C)))
  have hv : v ≫ Spec.map (CommRingCat.ofHom (algebraMap K C)) =
      t ≫ Spec.map (CommRingCat.ofHom (algebraMap K F)) := by
    have hb : b.left ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap K F)) := b.w
    rw [← hb, ← Category.assoc, ht, Category.assoc]
    exact (Category.assoc _ _ _).trans (congrArg (fun f => p ≫ f) pullback.condition.symm)
  let r := pullback.lift v t hv
  have hr : r ≫ scalarExtensionFamilyMap K C F X b = p := by
    apply pullback.hom_ext
    · change (r ≫ pullback.lift _ _ _) ≫ pullback.fst _ _ = p ≫ pullback.fst _ _
      rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_snd]
      exact ht
    · change (r ≫ pullback.lift _ _ _) ≫ pullback.snd _ _ = p ≫ pullback.snd _ _
      rw [Category.assoc, pullback.lift_snd, pullback.lift_fst]
  have hy := countable_scalarExtension_family_range_in_open K C F X b U hU
    (r (IsLocalRing.closedPoint L))
  exact (congrArg (fun f => f (IsLocalRing.closedPoint L) ∈ U) hr).mp hy

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.CountableRankSchemePoints.Construction
