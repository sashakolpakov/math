import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.ComplexBasisGluing

/-! # Complex Basis Gluing Large -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.ComplexBasisGluingLarge

noncomputable section

/-! Basis gluing for sheaf complexes with coefficients in the larger
module universe used by the original crystalline resolution. -/
open _root_.CategoryTheory Opposite _root_.TopologicalSpace
universe u v w z
variable (D : Type u) [Category.{v} D] [Abelian D] (X : TopCat.{w})

abbrev evaluation (U : Opens X) :=
  sheafToPresheaf (Opens.grothendieckTopology X) D ⋙
    (CategoryTheory.evaluation (Opens X)ᵒᵖ D).obj (op U)

abbrev sections (F : CochainComplex (Sheaf (Opens.grothendieckTopology X) D) ℕ)
    (U : Opens X) :=
  ((ComplexBasisGluingLarge.evaluation D X U).mapHomologicalComplex (.up ℕ)).obj F

def restriction (F : CochainComplex (Sheaf (Opens.grothendieckTopology X) D) ℕ)
    {U V : Opens X} (i : V ⟶ U) : sections D X F U ⟶ sections D X F V where
  f n := (F.X n).obj.map i.op
  comm' n m _ := (F.d n m).hom.naturality i.op

variable {D X} {ι : Type z} (B : ι → Opens X)
  (F G : CochainComplex (Sheaf (Opens.grothendieckTopology X) D) ℕ)

structure BasisMap where
  app : ∀ i, sections D X F (B i) ⟶ sections D X G (B i)
  naturality : ∀ i j (h : B i ≤ B j),
    app j ≫ restriction D X G (homOfLE h) =
      restriction D X F (homOfLE h) ≫ app i

namespace BasisMap
variable {B F G} (a : BasisMap B F G)

def presheafMap (n : ℕ) :
    (inducedFunctor B).op ⋙ (F.X n).obj ⟶ (inducedFunctor B).op ⋙ (G.X n).obj where
  app i := (a.app i.unop).f n
  naturality {i j} h :=
    (congrArg (fun f => f.f n) (a.naturality j.unop i.unop h.unop.hom.le)).symm

variable (hB : Opens.IsBasis (Set.range B))

def degreeMap (n : ℕ) : F.X n ⟶ G.X n :=
  ⟨TopCat.Sheaf.restrictHomEquivHom (F.X n).obj (G.X n) hB (a.presheafMap n)⟩

theorem degreeMap_app (n : ℕ) (i : ι) :
    (a.degreeMap hB n).hom.app (op (B i)) = (a.app i).f n :=
  TopCat.Sheaf.extend_hom_app (F.X n).obj (G.X n) hB (a.presheafMap n) i

def glue : F ⟶ G where
  f := a.degreeMap hB
  comm' n m hnm := by
    apply Sheaf.hom_ext
    apply TopCat.Sheaf.hom_ext (F.X n).obj (G.X m) hB
    intro i
    change (a.degreeMap hB n).hom.app (op (B i)) ≫ (G.d n m).hom.app (op (B i)) =
      (F.d n m).hom.app (op (B i)) ≫ (a.degreeMap hB m).hom.app (op (B i))
    rw [BasisMap.degreeMap_app, BasisMap.degreeMap_app]
    exact (a.app i).comm n m

theorem glue_app (n : ℕ) (i : ι) :
    ((a.glue hB).f n).hom.app (op (B i)) = (a.app i).f n :=
  a.degreeMap_app hB n i

theorem glue_unique (g : F ⟶ G)
    (hg : ∀ n i, (g.f n).hom.app (op (B i)) = (a.app i).f n) : g = a.glue hB := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply Sheaf.hom_ext
  apply TopCat.Sheaf.hom_ext (F.X n).obj (G.X n) hB
  intro i
  rw [glue_app, hg]

end BasisMap

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.ComplexBasisGluingLarge
