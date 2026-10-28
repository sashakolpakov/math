import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Epi

/-! # Abelian Quotient -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AbelianQuotient.Construction

/-!
# The abelian quotient after the affine-orbit neighborhood step

This module uses the exact abelian-scheme bundle of the FiniteDescent specification,
without importing its statement stub. The intermediate theorem below keeps
the still-unproved affine-orbit neighborhood condition explicit.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u v

theorem jointlyMono_left {C : Type u} [Category.{v} C] {S : C}
    {R A : Over S} (s t : R ⟶ A) [JointlyMono₂ s t] : JointlyMono₂ s.left t.left := by
  constructor
  intro Z f g h₁ h₂
  have hg : g ≫ R.hom = f ≫ R.hom := by
    rw [← s.w, ← Category.assoc, ← Category.assoc, h₁]
  let f' : Over.mk (f ≫ R.hom) ⟶ R := Over.homMk f rfl
  let g' : Over.mk (f ≫ R.hom) ⟶ R := Over.homMk g hg
  exact congrArg (fun k => k.left) (JointlyMono₂.right_cancellation f' g'
    (Over.OverMorphism.ext h₁) (Over.OverMorphism.ext h₂))

/-- The scheme-theoretic translation relation, obtained from the actual
group relation in the category over the base. -/
noncomputable def translationSchemeEquivalenceRelation
    {S : Scheme.{u}} {A H : Over S} [GrpObj A] [GrpObj H]
    (i : H ⟶ A) [IsMonHom i] [Mono i] :
    CategoryTheory.EquivalenceRelation (snd H A).left (Epi.Construction.translation i).left := by
  let e := Epi.Construction.translationEquivalenceRelation i
  let : JointlyMono₂ (snd H A) (Epi.Construction.translation i) := e.toJointlyMono₂
  let : JointlyMono₂ ((Over.forget S).map (snd H A))
      ((Over.forget S).map (Epi.Construction.translation i)) := jointlyMono_left (snd H A) (Epi.Construction.translation i)
  exact
    { __ := e.toReflexiveRelation.map (Over.forget S)
      __ := e.toSymmetricRelation.map (Over.forget S)
      __ := e.toTransitiveRelation.map (Over.forget S) }

/-- A proper, smooth, commutative group scheme with geometrically connected
fibers, with the same fields as the FiniteDescent statement bundle. -/
structure AbelianScheme (S : Scheme.{u}) where
  toOver : Over S
  [group : GrpObj toOver]
  [commutative : IsCommMonObj toOver]
  [proper : IsProper toOver.hom]
  [smooth : Smooth toOver.hom]
  [connected : GeometricallyConnected toOver.hom]

attribute [instance] AbelianScheme.group AbelianScheme.commutative
  AbelianScheme.proper AbelianScheme.smooth AbelianScheme.connected

def FiniteLocallyFree {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f

/-- All conclusions of FiniteDescent follow from the remaining affine-orbit
neighborhood step. The quotient and all its structures are constructed. -/
theorem exists_abelian_scheme_quotient_of_affine_orbits
    (S : Scheme.{u}) (A : AbelianScheme S) (H : Over S) [GrpObj H]
    (i : H ⟶ A.toOver) [IsMonHom i]
    (hi : IsClosedImmersion i.left) (hH : FiniteLocallyFree H.hom)
    (hOrbit : ∀ x : A.toOver.left, ∃ U : A.toOver.left.Opens, IsAffineOpen U ∧
      ∀ y, Invariant.Construction.InvariantCore.Related (snd H A.toOver).left (Epi.Construction.translation i).left x y → y ∈ U) :
    ∃ (B : AbelianScheme S) (q : A.toOver ⟶ B.toOver),
      IsMonHom q ∧ FiniteLocallyFree q.left ∧ Surjective q.left ∧
      (∀ (T : Over S) (a : T ⟶ A.toOver),
        a ≫ q = 1 ↔ ∃! h : T ⟶ H, h ≫ i = a) ∧
      (∀ (T : Over S) (f : A.toOver ⟶ T),
        (∀ (U : Over S) (a : U ⟶ A.toOver) (h : U ⟶ H),
          ((h ≫ i) * a) ≫ f = a ≫ f) →
        ∃! g : B.toOver ⟶ T, q ≫ g = f) := by
  let := hi
  let := hH.1
  let := hH.2.1
  let := hH.2.2
  have : Mono i := Over.mono_of_mono_left i
  have hs : IsPullback (fst H A.toOver).left (snd H A.toOver).left H.hom A.toOver.hom :=
    IsPullback.of_hasPullback H.hom A.toOver.hom
  have ha : (snd H A.toOver).left ≫ A.toOver.hom = (Epi.Construction.translation i).left ≫ A.toOver.hom :=
    (snd H A.toOver).w.trans (Epi.Construction.translation i).w.symm
  obtain ⟨Q, π, hfin, hflat, hfp, hsurj, hk, hu⟩ := OrbitQuotientExists.Construction.OrbitQuotient.exists_quotient
    H.hom A.toOver.hom (fst H A.toOver).left (snd H A.toOver).left (Epi.Construction.translation i).left
    hs (translationSchemeEquivalenceRelation i) ha hOrbit
  let := hfin
  let := hflat
  let := hfp
  let := hsurj
  obtain ⟨b, hb, _⟩ := hu S A.toOver.hom ha
  let B₀ : Over S := Over.mk b
  let q : A.toOver ⟶ B₀ := Over.homMk π hb
  have : IsFinite q.left := hfin
  have : Flat q.left := hflat
  have : LocallyOfFinitePresentation q.left := hfp
  have : Surjective q.left := hsurj
  obtain ⟨g, hcomm, hmon, hker⟩ := Epi.Construction.commutativeGroup_of_translation_kernelPair i q hk
  let := g
  let := hcomm
  let := hmon
  obtain ⟨hproper, hsmooth, hconn⟩ := Epi.Construction.quotient_geometric_properties q
  let B : AbelianScheme S :=
    { toOver := B₀, group := g, commutative := hcomm,
      proper := hproper, smooth := hsmooth, connected := hconn }
  refine ⟨B, q, hmon, ⟨hfin, hflat, hfp⟩, hsurj, hker, ?_⟩
  intro T f hf
  exact Epi.Construction.quotient_universal_property i q hker T f hf

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AbelianQuotient.Construction
