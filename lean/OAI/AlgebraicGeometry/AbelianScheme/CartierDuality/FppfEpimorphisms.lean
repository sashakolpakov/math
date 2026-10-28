import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RepresentedMorphisms
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntrinsicQuotients
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Fppf Epimorphisms -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FppfEpimorphisms

noncomputable section

/-!
# CartierDuality: fppf group projections induce epimorphisms of the actual represented sheaves
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.Schemes

/-- A faithfully flat locally finitely presented morphism over the
base is a singleton covering on the relative big fppf site. -/
theorem singleton_fppf_over_cover {S : Scheme.{u}} {V T : Over S} (p : V ⟶ T)
    [Flat p.left] [Surjective p.left] [LocallyOfFinitePresentation p.left] :
    Sieve.generate (Presieve.singleton p) ∈ (Scheme.fppfTopology.over S) T := by
  rw [GrothendieckTopology.mem_over_iff, ← Presieve.ofArrows_pUnit.{0} p]
  change Sieve.overEquiv T (Sieve.ofArrows (fun _ : PUnit => V) (fun _ => p)) ∈ Scheme.fppfTopology T.left
  rw [Sieve.overEquiv_ofArrows]
  simpa only [Sieve.ofArrows, Presieve.ofArrows_pUnit] using
    (Precoverage.generate_mem_toGrothendieck p.left.singleton_mem_fppfPrecoverage)

/-- A native fppf group projection is locally surjective on the
actual commutative fppf sheaves. Lifts are supplied by scheme pullbacks. -/
theorem representedFppfAbMap_locallySurjective {S : Scheme.{u}} {G H : Grp (Over S)}
    [IsCommMonObj G.X] [IsCommMonObj H.X] (q : G ⟶ H)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left] :
    Sheaf.IsLocallySurjective (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap q) := by
  constructor
  intro T x
  obtain ⟨x⟩ := x
  let V := pullback q.hom.hom x
  let p : V ⟶ T := pullback.snd q.hom.hom x
  let a : V ⟶ G.X := pullback.fst q.hom.hom x
  have hp : IsPullback a.left p.left q.hom.hom.left x.left :=
    (IsPullback.of_hasPullback q.hom.hom x).map (Over.forget S)
  let : Flat p.left := MorphismProperty.of_isPullback hp inferInstance
  let : Surjective p.left := MorphismProperty.of_isPullback hp inferInstance
  let : LocallyOfFinitePresentation p.left := MorphismProperty.of_isPullback hp inferInstance
  apply (Scheme.fppfTopology.over S).superset_covering _ (singleton_fppf_over_cover p)
  rw [Sieve.generate_le_iff]
  intro W f hf
  cases hf
  refine ⟨ULift.up a, ?_⟩
  exact (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_apply q V a).trans
    (congrArg ULift.up (pullback.condition (f := q.hom.hom) (g := x)))

/-- A native fppf group projection is an epimorphism of the actual
commutative fppf sheaves. -/
theorem representedFppfAbMap_epi {S : Scheme.{u}} {G H : Grp (Over S)}
    [IsCommMonObj G.X] [IsCommMonObj H.X] (q : G ⟶ H)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left] : Epi (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap q) := by
  let : Sheaf.IsLocallySurjective (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap q) := representedFppfAbMap_locallySurjective q
  infer_instance

end Construction.Schemes

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FppfEpimorphisms
