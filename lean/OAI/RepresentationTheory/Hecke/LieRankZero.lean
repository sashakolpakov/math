import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks
import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors

/-! # Lie Rank Zero -/

namespace OAI.RepresentationTheory.Hecke.LieRankZero.OrdinaryCharacterIntrinsic

noncomputable section

/-! Detect zero Lie rank using the actual dual-number eigenspace.
Every infinitesimal eigenpoint in characteristic q lies in the q-torsion
block fixed by its coefficient projector. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {k O : Type} [Field k] [CommRing O] {g : ℕ}
  (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (τ : O →+* k)

def lieIdentityPoint : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.LieEigenpoints A ρ τ :=
  ⟨1, MonObj.comp_one _, fun a => (MonObj.one_comp (ρ.map a)).trans (MonObj.comp_one _).symm⟩

theorem hasLieRank_zero_eq_one (h : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A ρ τ 0)
    (x : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.LieEigenpoints A ρ τ) : x.val = 1 := by
  obtain ⟨e, _, _⟩ := h
  have he : e.symm x = e.symm (lieIdentityPoint A ρ τ) := Subsingleton.elim _ _
  exact congrArg Subtype.val (e.symm.injective he)

theorem hasLieRank_eq_zero_of_points {r : ℕ} (h : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A ρ τ r)
    (hz : ∀ x : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.LieEigenpoints A ρ τ, x.val = 1) : r = 0 := by
  by_contra hr
  obtain ⟨e, _, _⟩ := h
  have he : (0 : Fin r → k) = 1 :=
    e.injective (Subtype.ext ((hz (e 0)).trans (hz (e 1)).symm))
  exact zero_ne_one (congrFun he ⟨0, Nat.pos_of_ne_zero hr⟩)

theorem dualNumberScalar_zero (k : Type) [Field k] :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar k 0 = toUnit (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k) ≫ AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale k 0).toRingHom) =
    Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫
      Spec.map (CommRingCat.ofHom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction k))
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  apply TrivSqZeroExt.ext
  · change (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale k 0 z).fst = (algebraMap k (DualNumber k) z.fst).fst
    simp [AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale, TrivSqZeroExt.algebraMap_eq_inl]
  · change (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale k 0 z).snd = 0
    simp [AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale]

theorem dualNumberScalar_one (k : Type) [Field k] : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar k 1 = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale k 1).toRingHom) = 𝟙 _
  have h : (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale k 1).toRingHom = RingHom.id (DualNumber k) := by
    ext z <;> simp [AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale]
  rw [h]
  exact Spec.map_id _

theorem lieEigenpoint_pow_char (q : ℕ) [CharP k q]
    (x : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.LieEigenpoints A ρ τ) : x.val ^ q = 1 := by
  have h := x.property.2 (q : O)
  rw [AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors.integralAction_natCast, MonObj.comp_pow, Category.comp_id,
    map_natCast, CharP.cast_eq_zero, dualNumberScalar_zero,
    Category.assoc, x.property.1, MonObj.comp_one] at h
  exact h

def lieEigenpointBlockLift (q : ℕ) [CharP k q] (e : O) (he : τ e = 1)
    (x : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.LieEigenpoints A ρ τ) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k ⟶ AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors.idempotentBlockScheme A ρ q e :=
  (AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors.idempotentBlockPointsEquiv A ρ q e (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k)).symm
    ⟨x.val, lieEigenpoint_pow_char A ρ τ q x,
      (x.property.2 e).trans (by rw [he, dualNumberScalar_one, Category.id_comp])⟩

theorem lieEigenpointBlockLift_inclusion (q : ℕ) [CharP k q] (e : O) (he : τ e = 1)
    (x : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.LieEigenpoints A ρ τ) :
    lieEigenpointBlockLift A ρ τ q e he x ≫ AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors.idempotentBlockInclusion A ρ q e = x.val :=
  congrArg Subtype.val
    ((AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors.idempotentBlockPointsEquiv A ρ q e (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k)).apply_symm_apply _)

end

end OAI.RepresentationTheory.Hecke.LieRankZero.OrdinaryCharacterIntrinsic
