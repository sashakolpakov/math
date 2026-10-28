import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Etale Subgroup -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels

/-! Finite flat subgroup models inside an étale group are finite étale. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {H T : Over S} [GrpObj H]
variable [IsFinite H.hom] [Etale H.hom]
variable {F : SubgroupFunctor.RelativeSubgroup H T} (R : F.Model)

noncomputable abbrev inclusion : R.carrier ⟶ T ⊗ H := lift R.toBase R.toGroup

instance inclusion_closed : IsClosedImmersion (inclusion R).left := R.closedImmersion

theorem etale : Etale R.toBase.left := by
  have hp : Etale (fst T H).left :=
    inferInstanceAs (Etale (pullback.fst T.hom H.hom))
  have hc : FormallyUnramified ((inclusion R).left ≫ (fst T H).left) :=
    MorphismProperty.comp_mem (@FormallyUnramified) _ _ inferInstance inferInstance
  have he : (inclusion R).left ≫ (fst T H).left = R.toBase.left :=
    congrArg (fun f => f.left) (lift_fst R.toBase R.toGroup)
  have : FormallyUnramified R.toBase.left := he ▸ hc
  have : Flat R.toBase.left := R.flat
  have : LocallyOfFinitePresentation R.toBase.left := R.finitePresentation
  exact Etale.of_formallyUnramified_of_flat R.toBase.left

instance inclusion_etale : Etale (inclusion R).left := by
  have hp : Etale (fst T H).left :=
    inferInstanceAs (Etale (pullback.fst T.hom H.hom))
  have he : (inclusion R).left ≫ (fst T H).left = R.toBase.left :=
    congrArg (fun f => f.left) (lift_fst R.toBase R.toGroup)
  have : Etale ((inclusion R).left ≫ (fst T H).left) := he.symm ▸ etale R
  exact Etale.of_comp (inclusion R).left (fst T H).left

instance inclusion_open : IsOpenImmersion (inclusion R).left :=
  IsOpenImmersion.of_flat_of_mono _

omit [IsFinite H.hom] [Etale H.hom] in
theorem membership_iff_factor {X : Over S} (t : X ⟶ T) (a : X ⟶ H) :
    a ∈ F.points X t ↔ ∃ h : X ⟶ R.carrier, h ≫ inclusion R = lift t a := by
  rw [R.points_iff]
  constructor
  · rintro ⟨h, hb, hg⟩
    refine ⟨h, ?_⟩
    apply hom_ext
    · simpa only [Category.assoc, lift_fst] using hb
    · simpa only [Category.assoc, lift_snd] using hg
  · rintro ⟨h, hh⟩
    refine ⟨h, ?_, ?_⟩
    · simpa only [Category.assoc, lift_fst] using congrArg (fun f => f ≫ fst T H) hh
    · simpa only [Category.assoc, lift_snd] using congrArg (fun f => f ≫ snd T H) hh

theorem membership_iff_range {X : Over S} (t : X ⟶ T) (a : X ⟶ H) :
    a ∈ F.points X t ↔ Set.range (lift t a).left ⊆ Set.range (inclusion R).left := by
  rw [membership_iff_factor R t a]
  constructor
  · rintro ⟨h, hh⟩ _ ⟨x, rfl⟩
    exact ⟨h.left x, (congrArg (fun f => f.left x) hh)⟩
  · intro hr
    let l := IsOpenImmersion.lift (inclusion R).left (lift t a).left hr
    have hl : l ≫ (inclusion R).left = (lift t a).left := IsOpenImmersion.lift_fac _ _ _
    have hb : l ≫ R.carrier.hom = X.hom := by
      rw [← (inclusion R).w, ← Category.assoc, hl, (lift t a).w]
    exact ⟨Over.homMk l hb, Over.OverMorphism.ext hl⟩

include R in
/-- A finite étale subgroup is determined on all test schemes by its
geometric fibers, even when the test schemes have nilpotents. -/
theorem membership_iff_geometric {X : Over S} (t : X ⟶ T) (a : X ⟶ H) :
    a ∈ F.points X t ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K]
        (s : Spec (CommRingCat.of K) ⟶ S) (x : Over.mk s ⟶ X),
        x ≫ a ∈ F.points (Over.mk s) (x ≫ t) := by
  constructor
  · intro ha K hK hclosed s x
    exact F.naturality x t ha
  · intro ha
    apply (membership_iff_range R t a).mpr
    rintro _ ⟨x, rfl⟩
    let K := AlgebraicClosure (X.left.residueField x)
    let i := Spec.map (CommRingCat.ofHom (algebraMap (X.left.residueField x) K))
    let p := i ≫ X.left.fromSpecResidueField x
    let s := p ≫ X.hom
    let z : Over.mk s ⟶ X := Over.homMk p rfl
    have hr := (membership_iff_range R (z ≫ t) (z ≫ a)).mp (ha K s z)
    have he := hr ⟨(default : Spec (CommRingCat.of K)), rfl⟩
    have hl : lift (z ≫ t) (z ≫ a) = z ≫ lift t a := (comp_lift z t a).symm
    rw [hl] at he
    change (lift t a).left (X.left.fromSpecResidueField x (i default)) ∈
      Set.range (inclusion R).left at he
    rwa [Scheme.fromSpecResidueField_apply] at he

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels
