import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.SiteDensity
import Mathlib.AlgebraicGeometry.Sites.BigZariski

/-! # Disjoint Sections -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.DisjointSections.Construction

noncomputable section

/-!
# Completion: gluing sections over actual disjoint unions

Arbitrary sections on the components of a disjoint union glue uniquely
in the actual pro-étale site. Distinct components have empty overlap.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

variable {X : Scheme.{u}}

/-- A sheaf has at most one section over an empty site object. -/
theorem proEtaleSheaf_empty_ext (F : Sheaf (Scheme.ProEt.topology X) (Type w))
    (U : X.ProEt) [IsEmpty U.left] (x y : F.obj.obj (op U)) : x = y := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).mp F.property
  apply (hF ⊥ (Scheme.ProEt.bot_mem_topology U)).isSeparatedFor.ext
  intro V f hf
  exact False.elim hf

variable {ι : Type v} [Small.{u} ι] (Y : ι → X.ProEt)

/-- The ordinary disjoint union as an actual pro-étale site object. -/
def proEtaleDisjointUnion : X.ProEt := by
  have : WeaklyEtale (Sigma.desc (fun i => (Y i).hom)) :=
    IsZariskiLocalAtSource.sigmaDesc (fun i => (Y i).prop)
  exact Scheme.ProEt.mk (Sigma.desc (fun i => (Y i).hom))

/-- The component inclusion into the actual disjoint union. -/
def proEtaleDisjointInclusion (i : ι) : Y i ⟶ proEtaleDisjointUnion Y :=
  MorphismProperty.Over.homMk (Sigma.ι (fun j => (Y j).left) i) (by simp [proEtaleDisjointUnion])

/-- Maps from the components induce the actual map from their disjoint union. -/
def proEtaleDisjointDesc {U : X.ProEt} (p : ∀ i, Y i ⟶ U) : proEtaleDisjointUnion Y ⟶ U :=
  MorphismProperty.Over.homMk (Sigma.desc (fun i => (p i).left)) (by
    apply Sigma.hom_ext
    intro i
    simp [proEtaleDisjointUnion])

/-- The disjoint-union components give an actual covering family. -/
theorem proEtaleDisjoint_cover :
    Sieve.generate (Presieve.ofArrows Y (proEtaleDisjointInclusion Y)) ∈
      Scheme.ProEt.topology X (proEtaleDisjointUnion Y) := by
  apply Precoverage.generate_mem_toGrothendieck
  change (Presieve.ofArrows Y (proEtaleDisjointInclusion Y)).map
    (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
      Scheme.proetalePrecoverage (proEtaleDisjointUnion Y).left
  rw [Presieve.map_ofArrows]
  exact Scheme.zariskiPrecoverage_le_propQCPrecoverage _ (sigmaOpenCover (fun i => (Y i).left)).mem₀

/-- Independent sections on disjoint components glue uniquely. -/
theorem proEtaleSheaf_disjoint_sections (F : Sheaf (Scheme.ProEt.topology X) (Type w))
    (s : ∀ i, F.obj.obj (op (Y i))) :
    ∃! t : F.obj.obj (op (proEtaleDisjointUnion Y)),
      ∀ i, F.obj.map (proEtaleDisjointInclusion Y i).op t = s i := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).mp F.property
  apply (Presieve.isSheafFor_arrows_iff (P := F.obj) (π := proEtaleDisjointInclusion Y)).mp
    (hF.isSheafFor _ (proEtaleDisjoint_cover Y)) s
  intro i j W p q hpq
  have hh : p.left ≫ Sigma.ι (fun i => (Y i).left) i =
      q.left ≫ Sigma.ι (fun i => (Y i).left) j :=
    congrArg (fun k : W ⟶ proEtaleDisjointUnion Y => k.left) hpq
  by_cases hij : i = j
  · subst j
    have hpq' : p = q := MorphismProperty.Over.Hom.ext ((cancel_mono _).mp hh)
    rw [hpq']
  · have : IsEmpty W.left := isInitial_iff_isEmpty.mp
      ⟨IsInitial.ofCoproductDisjointOfCommSq hij
        (coproductIsCoproduct (fun i => (Y i).left)) p.left q.left hh⟩
    exact proEtaleSheaf_empty_ext F W _ _

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.DisjointSections.Construction
