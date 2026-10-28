import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AbelianQuotient
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FiniteImages
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GroupRepresentatives

/-! # Intrinsic Quotients -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntrinsicQuotients

noncomputable section

/-!
# CartierDuality: finite locally free quotients by finite locally free subgroup schemes
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.Schemes

/-- A finite group scheme has affine neighborhoods containing each
whole subgroup orbit: pull back an affine neighborhood in the base. -/
theorem finite_group_affine_orbits {S : Scheme.{u}} (G H : Grp (Over S))
    [IsFinite G.X.hom] (i : H ⟶ G) (x : G.X.left) :
    ∃ U : G.X.left.Opens, IsAffineOpen U ∧
      ∀ y, Quotients.FiniteDescent.Invariant.Construction.InvariantCore.Related (snd H.X G.X).left
        (Quotients.FiniteDescent.Epi.Construction.translation i.hom.hom).left x y → y ∈ U := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show G.X.hom x ∈ (⊤ : S.Opens) from trivial)
  refine ⟨G.X.hom ⁻¹ᵁ U, hU.preimage G.X.hom, ?_⟩
  rintro y ⟨z, hz, hz'⟩
  have hb : (snd H.X G.X).left ≫ G.X.hom = (Quotients.FiniteDescent.Epi.Construction.translation i.hom.hom).left ≫ G.X.hom :=
    (snd H.X G.X).w.trans (Quotients.FiniteDescent.Epi.Construction.translation i.hom.hom).w.symm
  have he : G.X.hom x = G.X.hom y := by
    simpa only [Scheme.Hom.comp_apply, hz, hz'] using congrArg (fun f => f z) hb
  change G.X.hom y ∈ U
  exact he ▸ hx

/-- Geometric quotient data with the native projection and the exact
subgroup kernel on every scheme-valued point. -/
structure NativeFiniteLocallyFreeQuotient {S : Scheme.{u}} {G H : Grp (Over S)} (i : H ⟶ G) where
  quotient : Grp (Over S)
  commutative : IsCommMonObj quotient.X
  finite : IsFinite quotient.X.hom
  flat : Flat quotient.X.hom
  finitelyPresented : LocallyOfFinitePresentation quotient.X.hom
  projection : G ⟶ quotient
  projectionFinite : IsFinite projection.hom.hom.left
  projectionFlat : Flat projection.hom.hom.left
  projectionFinitelyPresented : LocallyOfFinitePresentation projection.hom.hom.left
  projectionSurjective : Surjective projection.hom.hom.left
  kernel : ∀ (T : Over S) (x : T ⟶ G.X),
    x ≫ projection.hom.hom = 1 ↔ ∃! h : T ⟶ H.X, h ≫ i.hom.hom = x

/-- Quotients of finite locally free commutative group schemes by
finite locally free closed subgroup schemes are finite locally free.
The quotient scheme and all its properties are constructed. -/
def nativeFiniteLocallyFreeQuotient {S : Scheme.{u}} (G H : Grp (Over S))
    [IsCommMonObj G.X] [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    [IsFinite H.X.hom] [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom]
    (i : H ⟶ G) [IsClosedImmersion i.hom.hom.left] : NativeFiniteLocallyFreeQuotient i := by
  apply Classical.choice
  have : Mono i.hom.hom := Over.mono_of_mono_left i.hom.hom
  have hs : IsPullback (fst H.X G.X).left (snd H.X G.X).left H.X.hom G.X.hom :=
    IsPullback.of_hasPullback _ _
  have ha : (snd H.X G.X).left ≫ G.X.hom = (Quotients.FiniteDescent.Epi.Construction.translation i.hom.hom).left ≫ G.X.hom :=
    (snd H.X G.X).w.trans (Quotients.FiniteDescent.Epi.Construction.translation i.hom.hom).w.symm
  obtain ⟨Q, π, hfin, hflat, hfp, hsurj, hk, hu⟩ := Quotients.FiniteDescent.OrbitQuotientExists.Construction.OrbitQuotient.exists_quotient
    H.X.hom G.X.hom (fst H.X G.X).left (snd H.X G.X).left (Quotients.FiniteDescent.Epi.Construction.translation i.hom.hom).left
    hs (Quotients.FiniteDescent.AbelianQuotient.Construction.translationSchemeEquivalenceRelation i.hom.hom) ha (finite_group_affine_orbits G H i)
  obtain ⟨b, hb, _⟩ := hu S G.X.hom ha
  let B : Over S := Over.mk b
  let q : G.X ⟶ B := Over.homMk π hb
  let : IsFinite q.left := hfin
  let : Flat q.left := hflat
  let : LocallyOfFinitePresentation q.left := hfp
  let : Surjective q.left := hsurj
  obtain ⟨g, hcomm, hmon, hker⟩ := Quotients.FiniteDescent.Epi.Construction.commutativeGroup_of_translation_kernelPair i.hom.hom q hk
  let : GrpObj B := g
  let : IsCommMonObj B := hcomm
  let : IsMonHom q := hmon
  have hbProper : IsProper B.hom := Quotients.FiniteDescent.GroupOf.Construction.GroupGeometry.proper_of_finite_quotient q
  have hbFinite : IsFinite B.hom := by
    let : IsFinite (q.left ≫ B.hom) := q.w.symm ▸ inferInstanceAs (IsFinite G.X.hom)
    exact FiniteImages.Construction.Schemes.finite_of_proper_of_surjective_comp q.left B.hom
  have hbFlat : Flat B.hom := by
    let : Flat (q.left ≫ B.hom) := q.w.symm ▸ inferInstanceAs (Flat G.X.hom)
    exact Quotients.FiniteDescent.SchemeFiniteness.Construction.SchemeFinitenessDescent.flat q.left B.hom
  have hbFp : LocallyOfFinitePresentation B.hom := by
    let : LocallyOfFinitePresentation (q.left ≫ B.hom) :=
      q.w.symm ▸ inferInstanceAs (LocallyOfFinitePresentation G.X.hom)
    exact Quotients.FiniteDescent.SchemeFiniteness.Construction.SchemeFinitenessDescent.locallyOfFinitePresentation q.left B.hom
  exact ⟨{
    quotient := Grp.mk B
    commutative := hcomm
    finite := hbFinite
    flat := hbFlat
    finitelyPresented := hbFp
    projection := Grp.homMk q
    projectionFinite := hfin
    projectionFlat := hflat
    projectionFinitelyPresented := hfp
    projectionSurjective := hsurj
    kernel := hker
  }⟩

end Construction.Schemes

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntrinsicQuotients
