import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.ZMod.Basic

/-! # Subgroup Functor -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

/-!
# TorsionQuotient: geometric subgroup choices

A relative subgroup is specified by its subgroup of points on every test
scheme, naturally in the test scheme. A geometric model represents this
subgroup by a finite flat finitely presented scheme over the parameter base.
The joint monomorphism condition identifies the model with a subgroup of the
base-changed group scheme, rather than a cover of such a subgroup.

Models are only witnesses of a property of a subgroup of points. Consequently
isomorphic embeddings give the same choice, and no marking is chosen.
Neither a scheme representing the space of choices nor finite etaleness is
used in these definitions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

noncomputable def torsionScheme
    {S : Scheme.{u}} (A : Over S) [GrpObj A] (m : ℕ) : Over S :=
  equalizer ((𝟙 A : A ⟶ A) ^ m) (1 : A ⟶ A)

variable {S : Scheme.{u}} {A : Over S} [GrpObj A]

/-- Inclusion of the actual scheme-theoretic m-torsion kernel. -/
noncomputable def torsionι (A : Over S) [GrpObj A] (m : ℕ) :
    torsionScheme A m ⟶ A :=
  equalizer.ι ((𝟙 A : A ⟶ A) ^ m) (1 : A ⟶ A)

/-- A test-scheme section killed by m factors through the kernel. -/
noncomputable def torsionLift {X : Over S} (m : ℕ) (a : X ⟶ A) (ha : a ^ m = 1) :
    X ⟶ torsionScheme A m :=
  equalizer.lift a (by
    simpa only [MonObj.comp_pow, Category.comp_id, MonObj.comp_one] using ha)

@[simp] theorem torsionLift_ι {X : Over S} (m : ℕ) (a : X ⟶ A) (ha : a ^ m = 1) :
    torsionLift m a ha ≫ torsionι A m = a :=
  equalizer.lift_ι _ _

theorem factors_through_torsion_iff {X : Over S} (m : ℕ) (a : X ⟶ A) :
    (∃ h : X ⟶ torsionScheme A m, h ≫ torsionι A m = a) ↔ a ^ m = 1 := by
  constructor
  · rintro ⟨h, rfl⟩
    have hi : torsionι A m ^ m = 1 := by
      unfold torsionι torsionScheme
      simpa only [MonObj.comp_pow, Category.comp_id, MonObj.comp_one] using
        equalizer.condition ((𝟙 A : A ⟶ A) ^ m) (1 : A ⟶ A)
    calc
      (h ≫ torsionι A m) ^ m = h ≫ (torsionι A m ^ m) :=
        (MonObj.comp_pow (torsionι A m) m h).symm
      _ = h ≫ (1 : torsionScheme A m ⟶ A) := congrArg (fun z => h ≫ z) hi
      _ = 1 := MonObj.comp_one h
  · intro ha
    exact ⟨torsionLift m a ha, torsionLift_ι m a ha⟩

/-- A subgroup of the functor of points of A over a variable T. -/
@[ext]
structure RelativeSubgroup (A : Over S) [GrpObj A] (T : Over S) where
  points : ∀ X : Over S, (X ⟶ T) → Subgroup (X ⟶ A)
  naturality : ∀ {X Y : Over S} (f : X ⟶ Y) (t : Y ⟶ T) {a : Y ⟶ A},
    a ∈ points Y t → f ≫ a ∈ points X (f ≫ t)

namespace RelativeSubgroup

variable {T U V : Over S}

/-- Base change reindexes the structure map of every test scheme. -/
def baseChange (F : RelativeSubgroup A T) (f : U ⟶ T) : RelativeSubgroup A U where
  points X t := F.points X (t ≫ f)
  naturality := by
    intro X Y g t a ha
    simpa only [Category.assoc] using F.naturality g (t ≫ f) ha

@[simp] theorem baseChange_id (F : RelativeSubgroup A T) :
    F.baseChange (𝟙 T) = F := by
  ext X t a
  simp [RelativeSubgroup.baseChange]

theorem baseChange_comp (F : RelativeSubgroup A T) (f : U ⟶ T) (g : V ⟶ U) :
    F.baseChange (g ≫ f) = (F.baseChange f).baseChange g := by
  ext X t a
  simp [RelativeSubgroup.baseChange, Category.assoc]

/-- A finite locally free model of the subgroup, with its actual embedding
encoded by joint monicity of the maps to T and A. -/
structure Model (F : RelativeSubgroup A T) where
  carrier : Over S
  toBase : carrier ⟶ T
  toGroup : carrier ⟶ A
  finite : IsFinite toBase.left
  flat : Flat toBase.left
  finitePresentation : LocallyOfFinitePresentation toBase.left
  jointly_monic : ∀ (X : Over S) (h k : X ⟶ carrier),
    h ≫ toBase = k ≫ toBase → h ≫ toGroup = k ≫ toGroup → h = k
  points_iff : ∀ (X : Over S) (t : X ⟶ T) (a : X ⟶ A),
    a ∈ F.points X t ↔ ∃ h : X ⟶ carrier, h ≫ toBase = t ∧ h ≫ toGroup = a

namespace Model

variable {F : RelativeSubgroup A T}

/-- The model after base change is the scheme-theoretic fiber product. -/
noncomputable def baseChange (R : RelativeSubgroup.Model F) (f : U ⟶ T) : RelativeSubgroup.Model (F.baseChange f) where
  carrier := pullback R.toBase f
  toBase := pullback.snd R.toBase f
  toGroup := pullback.fst R.toBase f ≫ R.toGroup
  finite := by
    have sq := (IsPullback.of_hasPullback R.toBase f).map (Over.forget S)
    exact MorphismProperty.of_isPullback sq R.finite
  flat := by
    have sq := (IsPullback.of_hasPullback R.toBase f).map (Over.forget S)
    exact MorphismProperty.of_isPullback sq R.flat
  finitePresentation := by
    have sq := (IsPullback.of_hasPullback R.toBase f).map (Over.forget S)
    exact MorphismProperty.of_isPullback sq R.finitePresentation
  jointly_monic X h k hbase hgroup := by
    apply pullback.hom_ext
    · apply R.jointly_monic X
      · simpa only [Category.assoc, pullback.condition] using
          congrArg (fun z => z ≫ f) hbase
      · simpa only [Category.assoc] using hgroup
    · exact hbase
  points_iff X t a := by
    change a ∈ F.points X (t ≫ f) ↔ _
    rw [R.points_iff]
    constructor
    · rintro ⟨h, hbase, hgroup⟩
      refine ⟨pullback.lift h t hbase, ?_, ?_⟩
      · exact pullback.lift_snd h t hbase
      · simpa only [← Category.assoc, pullback.lift_fst] using hgroup
    · rintro ⟨h, hbase, hgroup⟩
      refine ⟨h ≫ pullback.fst R.toBase f, ?_, ?_⟩
      · simpa only [Category.assoc, pullback.condition] using
          congrArg (fun z => z ≫ f) hbase
      · simpa only [Category.assoc] using hgroup

/-- Over a separated group scheme, a finite model is a closed subgroup
of T ×[S] A. This is a consequence of the model data. -/
theorem closedImmersion [IsSeparated A.hom] (R : RelativeSubgroup.Model F) :
    IsClosedImmersion (lift R.toBase R.toGroup).left := by
  let j := lift R.toBase R.toGroup
  have hj : Mono j := by
    constructor
    intro X h k e
    apply R.jointly_monic X h k
    · simpa only [j, Category.assoc, lift_fst] using congrArg (fun z => z ≫ fst T A) e
    · simpa only [j, Category.assoc, lift_snd] using congrArg (fun z => z ≫ snd T A) e
  let : Mono j := hj
  let : IsFinite R.toBase.left := R.finite
  have hcomp : IsFinite (j.left ≫ (fst T A).left) := by
    change IsFinite (pullback.lift R.toBase.left R.toGroup.left
      (R.toBase.w.trans R.toGroup.w.symm) ≫ pullback.fst _ _)
    simpa only [pullback.lift_fst] using R.finite
  let : IsFinite (j.left ≫ (fst T A).left) := hcomp
  have hsep : IsSeparated (fst T A).left := by
    change IsSeparated (pullback.fst T.hom A.hom)
    infer_instance
  let : IsSeparated (fst T A).left := hsep
  have hfinite : IsFinite j.left := IsFinite.of_comp j.left (fst T A).left
  exact (IsClosedImmersion.iff_isFinite_and_mono j.left).mpr ⟨hfinite, inferInstance⟩

end Model

/-- Every section of this relative subgroup is killed by m. -/
def KilledBy (F : RelativeSubgroup A T) (m : ℕ) : Prop :=
  ∀ (X : Over S) (t : X ⟶ T) (a : X ⟶ A), a ∈ F.points X t → a ^ m = 1

/-- The geometric point groups have the prescribed finite module type.
For groups killed by m, their abstract abelian group determines their
ZMod m-module structure; thus a group isomorphism expresses this type.
The intended application has m invertible on S. -/
def HasModuleType (F : RelativeSubgroup A T) (M : Type u) [AddCommGroup M] : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) (t : Over.mk s ⟶ T),
    Nonempty (F.points (Over.mk s) t ≃* Multiplicative M)

namespace Model

variable {F : RelativeSubgroup A T} {m : ℕ}

/-- The model's inclusion is killed by m as a scheme morphism. -/
theorem toGroup_pow_eq_one (R : RelativeSubgroup.Model F) (h : F.KilledBy m) : R.toGroup ^ m = 1 := by
  apply h R.carrier R.toBase R.toGroup
  apply (R.points_iff R.carrier R.toBase R.toGroup).mpr
  exact ⟨𝟙 R.carrier, Category.id_comp _, Category.id_comp _⟩

/-- The representing subgroup has an actual morphism to A[m]. -/
noncomputable def toTorsion (R : RelativeSubgroup.Model F) (h : F.KilledBy m) :
    R.carrier ⟶ torsionScheme A m :=
  torsionLift m R.toGroup (R.toGroup_pow_eq_one h)

@[simp] theorem toTorsion_ι (R : RelativeSubgroup.Model F) (h : F.KilledBy m) :
    R.toTorsion h ≫ torsionι A m = R.toGroup :=
  torsionLift_ι _ _ _

end Model

end RelativeSubgroup

/-- An unmarked, finite locally free subgroup of A_T[m], recorded as its
functor of points. The model is a witness for the subgroup itself, not
for the parameter space of choices. -/
@[ext]
structure SubgroupChoice (A : Over S) [GrpObj A]
    (m : ℕ) (M : Type u) [AddCommGroup M] [Module (ZMod m) M] [Finite M]
    (T : Over S) where
  subgroup : RelativeSubgroup A T
  killed : subgroup.KilledBy m
  moduleType : subgroup.HasModuleType M
  geometric : Nonempty subgroup.Model

namespace SubgroupChoice

variable {m : ℕ} {M : Type u} [AddCommGroup M] [Module (ZMod m) M] [Finite M]
variable {T U V : Over S}

/-- Pullback of a subgroup choice; its model is the actual fiber product. -/
def baseChange (F : SubgroupChoice A m M T) (f : U ⟶ T) : SubgroupChoice A m M U where
  subgroup := F.subgroup.baseChange f
  killed X t a ha := F.killed X (t ≫ f) a ha
  moduleType := by
    intro K hK hclosed s t
    exact F.moduleType K s (t ≫ f)
  geometric := F.geometric.elim fun R => ⟨R.baseChange f⟩

@[simp] theorem baseChange_id (F : SubgroupChoice A m M T) :
    F.baseChange (𝟙 T) = F := by
  apply SubgroupChoice.ext
  exact F.subgroup.baseChange_id

theorem baseChange_comp (F : SubgroupChoice A m M T) (f : U ⟶ T) (g : V ⟶ U) :
    F.baseChange (g ≫ f) = (F.baseChange f).baseChange g := by
  apply SubgroupChoice.ext
  exact F.subgroup.baseChange_comp f g

end SubgroupChoice

/-- The geometric subgroup-choice functor. Its universe is one level above
the hom-sets because its elements are subfunctors on all test schemes. -/
def subgroupChoiceFunctor (A : Over S) [GrpObj A] [IsCommMonObj A]
    (m : ℕ) (M : Type u) [AddCommGroup M] [Module (ZMod m) M] [Finite M] :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := SubgroupChoice A m M T.unop
  map f := ↾fun F => F.baseChange f.unop
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro F
    exact F.baseChange_id
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro F
    exact F.baseChange_comp f.unop g.unop

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor
