import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

/-! # Subgroup Functor -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction

/-!
Concrete subgroup choices on the chosen local blocks for IsogenyQuotient. A block is
specified by an endomorphism lifting its projector on n-torsion; this lift
need not be idempotent on the abelian scheme itself. A subgroup
is supported on the block when the lift acts identically on all its
test-scheme sections. This is a subfunctor of TorsionQuotient's actual subgroup functor,
with a canonical forgetful map; it is not an unrelated presheaf placeholder.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A : Over S} [GrpObj A]

/-- Membership in the chosen block, expressed on all test schemes. -/
def SupportedOn {T : Over S} (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A T) (p : A ⟶ A) : Prop :=
  ∀ (X : Over S) (t : X ⟶ T) (a : X ⟶ A),
    a ∈ F.points X t → a ≫ p = a

theorem supportedOn_baseChange
    {T U : Over S} (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A T) (p : A ⟶ A)
    (hF : SupportedOn F p) (f : U ⟶ T) : SupportedOn (F.baseChange f) p := by
  intro X t a ha
  exact hF X (t ≫ f) a ha

/-- Support on a block is exactly one equation between actual morphisms
on the finite subgroup model. This is the bridge to its parameter locus. -/
theorem supportedOn_iff_model_equation
    {T : Over S} (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A T)
    (R : F.Model) (p : A ⟶ A) :
    SupportedOn F p ↔ R.toGroup ≫ p = R.toGroup := by
  constructor
  · intro h
    apply h R.carrier R.toBase R.toGroup
    exact (R.points_iff R.carrier R.toBase R.toGroup).mpr
      ⟨𝟙 R.carrier, Category.id_comp _, Category.id_comp _⟩
  · intro h X t a ha
    obtain ⟨x, _, hx⟩ := (R.points_iff X t a).mp ha
    rw [← hx, Category.assoc, h]

variable (A) [IsCommMonObj A]

/-- TorsionQuotient's subgroup choice, restricted by a genuine projector condition. -/
abbrev SupportedChoice
    (n : ℕ) (M : Type u) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (p : A ⟶ A) (T : Over S) :=
  {F : TorsionQuotient.SubgroupFunctor.SubgroupChoice A n M T // SupportedOn F.subgroup p}

/-- The functor of subgroups of the prescribed type on one chosen block. -/
def supportedSubgroupFunctor
    (n : ℕ) (M : Type u) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (p : A ⟶ A) : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := SupportedChoice A n M p T.unop
  map f := ↾fun F =>
    ⟨F.val.baseChange f.unop,
      supportedOn_baseChange F.val.subgroup p F.property f.unop⟩
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro F
    apply Subtype.ext
    exact F.val.baseChange_id
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro F
    apply Subtype.ext
    exact F.val.baseChange_comp f.unop g.unop

/-- The canonical link with the subgroup functor supplied by TorsionQuotient. -/
def forgetBlockSupport
    (n : ℕ) (M : Type u) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (p : A ⟶ A) :
    supportedSubgroupFunctor A n M p ⟶ TorsionQuotient.SubgroupFunctor.subgroupChoiceFunctor A n M where
  app _ := ↾Subtype.val
  naturality _ _ _ := rfl

/-- Forgetting block support is injective on every test scheme. -/
theorem forgetBlockSupport_injective
    (n : ℕ) (M : Type u) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (p : A ⟶ A) (T : (Over S)ᵒᵖ) :
    Function.Injective ((forgetBlockSupport A n M p).app T) :=
  Subtype.val_injective

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction
