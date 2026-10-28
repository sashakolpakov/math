import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.ComplexBasisGluingLarge

/-! # Complex Basis Extension -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.ComplexBasisExtension

noncomputable section

/-! Maps from a presheaf complex to a sheaf complex extend uniquely
from a basis. The source need not already satisfy the sheaf condition. -/
open _root_.CategoryTheory Opposite _root_.TopologicalSpace
universe u v w z
variable (D : Type u) [Category.{v} D] [Abelian D] (X : TopCat.{w})

abbrev underlying (G : CochainComplex (Sheaf (Opens.grothendieckTopology X) D) ℕ) :
    CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ :=
  ((sheafToPresheaf (Opens.grothendieckTopology X) D).mapHomologicalComplex (.up ℕ)).obj G

abbrev sections (F : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ) (U : Opens X) :=
  (((CategoryTheory.evaluation (Opens X)ᵒᵖ D).obj (op U)).mapHomologicalComplex (.up ℕ)).obj F

def restriction (F : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ)
    {U V : Opens X} (i : V ⟶ U) : sections D X F U ⟶ sections D X F V where
  f n := (F.X n).map i.op
  comm' n m _ := (F.d n m).naturality i.op

variable {D X} {ι : Type z} (B : ι → Opens X)
  (F : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ)
  (G : CochainComplex (Sheaf (Opens.grothendieckTopology X) D) ℕ)

structure BasisMap where
  app : ∀ i, sections D X F (B i) ⟶ sections D X (underlying D X G) (B i)
  naturality : ∀ i j (h : B i ≤ B j),
    app j ≫ restriction D X (underlying D X G) (homOfLE h) =
      restriction D X F (homOfLE h) ≫ app i

namespace BasisMap
variable {B F G} (a : BasisMap B F G)

def presheafMap (n : ℕ) :
    (inducedFunctor B).op ⋙ F.X n ⟶ (inducedFunctor B).op ⋙ (G.X n).obj where
  app i := (a.app i.unop).f n
  naturality {i j} h :=
    (congrArg (fun f => f.f n) (a.naturality j.unop i.unop h.unop.hom.le)).symm

variable (hB : Opens.IsBasis (Set.range B))

def degreeMap (n : ℕ) : F.X n ⟶ (G.X n).obj :=
  TopCat.Sheaf.restrictHomEquivHom (F.X n) (G.X n) hB (a.presheafMap n)

theorem degreeMap_app (n : ℕ) (i : ι) :
    (a.degreeMap hB n).app (op (B i)) = (a.app i).f n :=
  TopCat.Sheaf.extend_hom_app (F.X n) (G.X n) hB (a.presheafMap n) i

def map : F ⟶ underlying D X G where
  f := a.degreeMap hB
  comm' n m _ := by
    apply TopCat.Sheaf.hom_ext (F.X n) (G.X m) hB
    intro i
    change (a.degreeMap hB n).app (op (B i)) ≫ (G.d n m).hom.app (op (B i)) =
      (F.d n m).app (op (B i)) ≫ (a.degreeMap hB m).app (op (B i))
    rw [BasisMap.degreeMap_app, BasisMap.degreeMap_app]
    exact (a.app i).comm n m

theorem map_app (n : ℕ) (i : ι) :
    ((a.map hB).f n).app (op (B i)) = (a.app i).f n :=
  a.degreeMap_app hB n i

theorem unique (f : F ⟶ underlying D X G)
    (hf : ∀ n i, (f.f n).app (op (B i)) = (a.app i).f n) : f = a.map hB := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply TopCat.Sheaf.hom_ext (F.X n) (G.X n) hB
  intro i
  rw [map_app, hf]

end BasisMap

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.ComplexBasisExtension
