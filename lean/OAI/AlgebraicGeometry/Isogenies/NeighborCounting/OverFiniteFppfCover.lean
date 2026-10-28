import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FiniteFppfCover
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.AlgebraicGeometry.Limits

/-! # Over Finite Fppf Cover -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OverFiniteFppfCover

noncomputable section

/-! Finite affine refinements retain the original base scheme and all
cover arrows, including their covering-sieve membership. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FiniteFppfCover

variable {S : Scheme.{u}} {Y : Over S} {R : Sieve Y}

def underlyingFamily [CompactSpace Y.left] (hR : R ∈ (Scheme.fppfTopology.over S) Y) :
    FiniteFppfCover.Family Y.left (Sieve.overEquiv Y R) :=
  FiniteFppfCover.finiteRefinement ((Scheme.fppfTopology.mem_over_iff R).mp hR)

variable (D : FiniteFppfCover.Family Y.left (Sieve.overEquiv Y R))

def coverObject (i : Fin D.n) : Over S := Over.mk (D.map i ≫ Y.hom)

def coverMap (i : Fin D.n) : coverObject D i ⟶ Y := Over.homMk (D.map i) rfl

theorem coverMap_member (i : Fin D.n) : R (coverMap D i) :=
  (Sieve.overEquiv_iff R (D.map i)).mp (D.member i)

def coverTotal : Over S := Over.mk (FiniteFppfCover.projection D ≫ Y.hom)

def coverProjection : coverTotal D ⟶ Y := Over.homMk (FiniteFppfCover.projection D) rfl

def coverInclusion (i : Fin D.n) : coverObject D i ⟶ coverTotal D :=
  Over.homMk (Sigma.ι D.source i) (by
    change Sigma.ι D.source i ≫ (Sigma.desc D.map ≫ Y.hom) = D.map i ≫ Y.hom
    rw [← Category.assoc, Sigma.ι_comp_desc])

theorem coverInclusion_projection (i : Fin D.n) :
    coverInclusion D i ≫ coverProjection D = coverMap D i := by
  apply Over.OverMorphism.ext
  exact Sigma.ι_comp_desc D.map i

instance coverInclusion_open (i : Fin D.n) : IsOpenImmersion (coverInclusion D i).left :=
  inferInstanceAs (IsOpenImmersion (Sigma.ι D.source i))

theorem coverInclusion_covers (x : (coverTotal D).left) :
    ∃ i, ∃ y : (coverObject D i).left, (coverInclusion D i).left y = x :=
  (sigmaOpenCover D.source).exists_eq x

theorem coverInclusion_disjoint :
    Pairwise (fun i j ↦ Disjoint (coverInclusion D i).left.opensRange (coverInclusion D j).left.opensRange) :=
  fun i j hij ↦ disjoint_opensRange_sigmaι D.source i j hij

instance coverTotal_affine : IsAffine (coverTotal D).left := inferInstanceAs (IsAffine (FiniteFppfCover.total D))

instance coverProjection_flat : Flat (coverProjection D).left := inferInstanceAs (Flat (FiniteFppfCover.projection D))

instance coverProjection_surjective : Surjective (coverProjection D).left :=
  inferInstanceAs (Surjective (FiniteFppfCover.projection D))

instance coverProjection_quasiCompact [QuasiSeparatedSpace Y.left] : QuasiCompact (coverProjection D).left :=
  inferInstanceAs (QuasiCompact (FiniteFppfCover.projection D))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OverFiniteFppfCover
