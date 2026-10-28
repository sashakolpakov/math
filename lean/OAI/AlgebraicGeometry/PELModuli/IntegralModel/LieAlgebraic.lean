import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LiePoints
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

/-! # Lie Algebraic -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieAlgebraic

noncomputable section

section

/-! Scalar multiplication in the algebraic Lie module is the actual
dual-number scaling map used in ReferenceFamily's Lie-rank predicate. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

namespace AlgebraicLie
open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

variable {k : Type} [Field k]

instance dualScale_isLocalHom (c : k) : IsLocalHom (AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale k c).toRingHom := by
  apply AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.isLocalHom_of_congruent (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k)
    (RingHom.id (DualNumber k))
  intro x
  change ((AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale k c x) - x).fst = 0
  rw [TrivSqZeroExt.fst_sub, AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale, TrivSqZeroExt.fst_map, sub_self]

theorem baseGerm_snd_zero (A : Over (Spec (.of k))) [MonObj A]
    (a : A.left.presheaf.stalk
      ((AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.unitPoint (DualNumberReduction.AlgebraicLie.dualBase k) A).hom
        (IsLocalRing.closedPoint (DualNumber k)))) :
    ((Scheme.stalkClosedPointTo
      (AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.unitPoint (DualNumberReduction.AlgebraicLie.dualBase k) A).hom).hom a).snd = 0 := by
  let g : Spec (.of (DualNumber k)) ⟶ A.left := (AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.unitPoint (DualNumberReduction.AlgebraicLie.dualBase k) A).hom
  let e := Scheme.stalkClosedPointTo g
  let q := CommRingCat.ofHom (AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale k 0).toRingHom
  let : IsLocalHom (e ≫ q).hom :=
    inferInstanceAs (IsLocalHom ((AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale k 0).toRingHom.comp e.hom))
  have h : AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.ofGerm A.left _ (e ≫ q) = AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.ofGerm A.left _ e := by
    simp only [AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.ofGerm, Spec.map_comp, Category.assoc]
    dsimp only [e]
    rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk g]
    exact congrArg Over.Hom.left (MonObj.comp_one (AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar k 0))
  have he := AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.ofGerm_injective _ (e ≫ q) e h
  have hv := congrArg (fun v => (v.hom a).snd) he
  change (AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale k 0 (e.hom a)).snd = (e.hom a).snd at hv
  change (e.hom a).snd = 0
  simpa only [AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale, TrivSqZeroExt.snd_map, zero_smul,
    LinearMap.zero_apply] using hv.symm

theorem point_smul (A : Over (Spec (.of k))) [MonObj A] (c : k) (v : LiePoints.AlgebraicLie.Space A) :
    LiePoints.AlgebraicLie.point A (c • v) = AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar k c ≫ LiePoints.AlgebraicLie.point A v := by
  let g : Spec (.of (DualNumber k)) ⟶ A.left := (AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.unitPoint (DualNumberReduction.AlgebraicLie.dualBase k) A).hom
  let e := Scheme.stalkClosedPointTo g
  have he (a) : (((algebraMap k (DualNumber k) c) • v.val).hom a) =
      AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale k c (v.val.hom a) := by
    rw [AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift.smul_hom]
    change e.hom a + algebraMap k (DualNumber k) c * (v.val.hom a - e.hom a) = _
    apply TrivSqZeroExt.ext
    · have h := v.val.congruent a
      change (v.val.hom a - e.hom a).fst = 0 at h
      have hf : (v.val.hom a).fst = (e.hom a).fst := sub_eq_zero.mp h
      simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_sub,
        TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl,
        AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale, TrivSqZeroExt.fst_map, hf, sub_self, mul_zero, add_zero]
    · have hz := baseGerm_snd_zero A a
      change (e.hom a).snd = 0 at hz
      simp only [TrivSqZeroExt.snd_add, DualNumber.snd_mul, TrivSqZeroExt.snd_sub,
        TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
        AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale, TrivSqZeroExt.snd_map, hz, sub_zero, zero_mul, add_zero,
        zero_add, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
  have hr : ((algebraMap k (DualNumber k) c) • v.val).hom =
      (AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale k c).toRingHom.comp v.val.hom := RingHom.ext he
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (((algebraMap k (DualNumber k) c) • v.val).hom)) ≫ _ =
    Spec.map (CommRingCat.ofHom (AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale k c).toRingHom) ≫
      (Spec.map (CommRingCat.ofHom v.val.hom) ≫ _)
  rw [hr]
  exact (congrArg (fun q => q ≫ A.left.fromSpecStalk _)
    (Spec.map_comp (CommRingCat.ofHom v.val.hom)
      (CommRingCat.ofHom (AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale k c).toRingHom))).trans (Category.assoc _ _ _)

end AlgebraicLie

end

section

/-! Actual group-scheme morphisms act linearly on algebraic Lie points,
in every characteristic. Their addition is pointwise group multiplication. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace AlgebraicLie
open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

variable {k : Type} [Field k] {A B C : Over (Spec (.of k))}
  [MonObj A] [MonObj B] [MonObj C]

theorem tangent_mem_relative (f : A ⟶ B) [IsMonHom f] (v : LiePoints.AlgebraicLie.Space A) :
    AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.tangent (DualNumberReduction.AlgebraicLie.dualBase k) (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) f v.val ∈
      AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.relative (DualNumberReduction.AlgebraicLie.dualBase k) (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) B := by
  apply AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.point_injective (DualNumberReduction.AlgebraicLie.dualBase k)
    (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) (𝟙_ (Over (Spec (.of k))))
  rw [AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.point_tangent, AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.point_tangent, AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.point_zero]
  change ((LiePoints.AlgebraicLie.point A v).left ≫ f.left) ≫ B.hom = (DualNumberReduction.AlgebraicLie.dualBase k)
  rw [Category.assoc, f.w]
  exact (LiePoints.AlgebraicLie.point A v).w

def map (f : A ⟶ B) [IsMonHom f] : LiePoints.AlgebraicLie.Space A →ₗ[k] LiePoints.AlgebraicLie.Space B where
  toFun v := ⟨AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.tangent (DualNumberReduction.AlgebraicLie.dualBase k)
    (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) f v.val, tangent_mem_relative f v⟩
  map_add' v w := Subtype.ext ((AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.tangent (DualNumberReduction.AlgebraicLie.dualBase k)
    (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) f).map_add v.val w.val)
  map_smul' c v := Subtype.ext ((AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.tangent (DualNumberReduction.AlgebraicLie.dualBase k)
    (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) f).map_smul (algebraMap k (DualNumber k) c) v.val)

theorem point_map (f : A ⟶ B) [IsMonHom f] (v : LiePoints.AlgebraicLie.Space A) :
    LiePoints.AlgebraicLie.point B (AlgebraicLie.map f v) = LiePoints.AlgebraicLie.point A v ≫ f :=
  Over.OverMorphism.ext (AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.point_tangent (DualNumberReduction.AlgebraicLie.dualBase k)
    (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) f v.val)

theorem map_congr (f h : A ⟶ B) [IsMonHom f] [IsMonHom h] (he : f = h) : AlgebraicLie.map f = AlgebraicLie.map h := by
  cases he
  rfl

theorem map_id : AlgebraicLie.map (𝟙 A) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply LiePoints.AlgebraicLie.point_injective A
  rw [point_map, Category.comp_id]
  rfl

theorem map_comp (f : A ⟶ B) (h : B ⟶ C) [IsMonHom f] [IsMonHom h] :
    AlgebraicLie.map (f ≫ h) = (AlgebraicLie.map h).comp (AlgebraicLie.map f) := by
  apply LinearMap.ext
  intro v
  apply LiePoints.AlgebraicLie.point_injective C
  change LiePoints.AlgebraicLie.point C (AlgebraicLie.map (f ≫ h) v) = LiePoints.AlgebraicLie.point C (AlgebraicLie.map h (AlgebraicLie.map f v))
  rw [point_map, point_map, point_map, Category.assoc]

theorem map_one : AlgebraicLie.map (1 : A ⟶ B) = 0 := by
  apply LinearMap.ext
  intro v
  apply LiePoints.AlgebraicLie.point_injective B
  rw [point_map, MonObj.comp_one]
  exact (LiePoints.AlgebraicLie.point_zero B).symm

theorem pointwise_mul_isMonHom [IsCommMonObj B] (f h : A ⟶ B) [IsMonHom f] [IsMonHom h] :
    IsMonHom (f * h) := by
  rw [Hom.mul_def]
  infer_instance

theorem map_mul [IsCommMonObj B] (f h : A ⟶ B) [IsMonHom f] [IsMonHom h] [IsMonHom (f * h)] :
    AlgebraicLie.map (f * h) = AlgebraicLie.map f + AlgebraicLie.map h := by
  apply LinearMap.ext
  intro v
  apply LiePoints.AlgebraicLie.point_injective B
  change LiePoints.AlgebraicLie.point B (AlgebraicLie.map (f * h) v) = LiePoints.AlgebraicLie.point B (AlgebraicLie.map f v + AlgebraicLie.map h v)
  rw [point_map, LiePoints.AlgebraicLie.point_add, point_map, point_map, MonObj.comp_mul]

end AlgebraicLie

end

/-! The actual differential of an integral action satisfies the ring
laws. The endomorphism family and each law are checked separately. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

namespace AlgebraicLie

variable {k R : Type} [Field k] [CommRing R] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A)

theorem action_zero : AlgebraicLie.map (ρ.map 0) = 0 :=
  (map_congr (ρ.map 0) (1 : A.scheme ⟶ A.scheme) ρ.map_zero).trans AlgebraicLie.map_one

theorem action_one : AlgebraicLie.map (ρ.map 1) = 1 :=
  (map_congr (ρ.map 1) (𝟙 A.scheme) ρ.map_one).trans map_id

theorem action_add (a b : R) : AlgebraicLie.map (ρ.map (a + b)) = AlgebraicLie.map (ρ.map a) + AlgebraicLie.map (ρ.map b) := by
  let : IsMonHom (ρ.map a * ρ.map b) := pointwise_mul_isMonHom (ρ.map a) (ρ.map b)
  exact (map_congr (ρ.map (a + b)) (ρ.map a * ρ.map b) (ρ.map_add a b)).trans
    (AlgebraicLie.map_mul (ρ.map a) (ρ.map b))

theorem action_mul (a b : R) : AlgebraicLie.map (ρ.map (a * b)) = AlgebraicLie.map (ρ.map a) * AlgebraicLie.map (ρ.map b) :=
  (map_congr (ρ.map (a * b)) (ρ.map b ≫ ρ.map a) (ρ.map_mul a b)).trans
    (AlgebraicLie.map_comp (ρ.map b) (ρ.map a))

def action (a : R) : Module.End k (LiePoints.AlgebraicLie.Space A.scheme) := AlgebraicLie.map (ρ.map a)

theorem action_apply (a : R) : action A ρ a = AlgebraicLie.map (ρ.map a) := rfl

end AlgebraicLie

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieAlgebraic
