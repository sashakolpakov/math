import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Sites.Abelian

/-! # Complex Basis Gluing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.ComplexBasisGluing

noncomputable section

/-! Compatible chain maps on an actual topological basis glue uniquely
to a morphism of the original sheaf complexes. -/

open _root_.CategoryTheory Opposite _root_.TopologicalSpace

universe u v

variable (R : Type u) [Ring R] (X : TopCat.{u})

abbrev evaluation (U : Opens X) :=
  sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) ⋙
    (CategoryTheory.evaluation (Opens X)ᵒᵖ (ModuleCat.{u} R)).obj (op U)

abbrev sections (F : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ) (U : Opens X) :=
  ((ComplexBasisGluing.evaluation R X U).mapHomologicalComplex (.up ℕ)).obj F

def restriction (F : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ)
    {U V : Opens X} (i : V ⟶ U) : sections R X F U ⟶ sections R X F V where
  f n := (F.X n).obj.map i.op
  comm' n m _ := (F.d n m).hom.naturality i.op

variable {R X} {ι : Type v} (B : ι → Opens X)
  (F G : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ)

structure BasisMap where
  app : ∀ i, sections R X F (B i) ⟶ sections R X G (B i)
  naturality : ∀ i j (h : B i ≤ B j),
    app j ≫ restriction R X G (homOfLE h) = restriction R X F (homOfLE h) ≫ app i

namespace BasisMap

variable {B F G} (D : BasisMap B F G)

def presheafMap (n : ℕ) :
    (inducedFunctor B).op ⋙ (F.X n).obj ⟶ (inducedFunctor B).op ⋙ (G.X n).obj where
  app i := (D.app i.unop).f n
  naturality {i j} h :=
    (congrArg (fun k => k.f n) (D.naturality j.unop i.unop h.unop.hom.le)).symm

variable (hB : Opens.IsBasis (Set.range B))

def degreeMap (n : ℕ) : F.X n ⟶ G.X n :=
  ⟨TopCat.Sheaf.restrictHomEquivHom (F.X n).obj (G.X n) hB (D.presheafMap n)⟩

theorem degreeMap_app (n : ℕ) (i : ι) :
    (D.degreeMap hB n).hom.app (op (B i)) = (D.app i).f n :=
  TopCat.Sheaf.extend_hom_app (F.X n).obj (G.X n) hB (D.presheafMap n) i

def glue : F ⟶ G where
  f := D.degreeMap hB
  comm' n m hnm := by
    apply Sheaf.hom_ext
    apply TopCat.Sheaf.hom_ext (F.X n).obj (G.X m) hB
    intro i
    change (D.degreeMap hB n).hom.app (op (B i)) ≫ (G.d n m).hom.app (op (B i)) =
      (F.d n m).hom.app (op (B i)) ≫ (D.degreeMap hB m).hom.app (op (B i))
    rw [BasisMap.degreeMap_app, BasisMap.degreeMap_app]
    exact (D.app i).comm n m

theorem glue_app (n : ℕ) (i : ι) :
    ((D.glue hB).f n).hom.app (op (B i)) = (D.app i).f n :=
  D.degreeMap_app hB n i

theorem glue_unique (g : F ⟶ G)
    (hg : ∀ n i, (g.f n).hom.app (op (B i)) = (D.app i).f n) : g = D.glue hB := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply Sheaf.hom_ext
  apply TopCat.Sheaf.hom_ext (F.X n).obj (G.X n) hB
  intro i
  rw [glue_app, hg]

end BasisMap

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.ComplexBasisGluing
