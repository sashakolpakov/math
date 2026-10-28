import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.HomologySquare
import OAI.NumberTheory.PadicHodge.IntegralComparison.MapHomologyIsoCompose

/-! # Homology Composition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.HomologyComposition

noncomputable section

/-! Canonical exact-functor homology coordinates compose with actual
complex isomorphisms, before any geometric complex is substituted. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A B D : Type*} [Category* A] [Category* B] [Category* D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B) (G : B ⥤ D)
  [F.Additive] [G.Additive] [F.PreservesHomology] [G.PreservesHomology]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

omit [G.PreservesHomology] in
theorem composite_preservesHomology : (F ⋙ G).PreservesHomology where
  preservesKernels _ _ f := by
    let := Functor.PreservesHomology.preservesKernel F f
    infer_instance
  preservesCokernels _ _ f := by
    let := Functor.PreservesHomology.preservesCokernel F f
    infer_instance

attribute [local instance] composite_preservesHomology

variable {ι : Type*} {s : ComplexShape ι}
  (K : HomologicalComplex A s) (L : HomologicalComplex B s) (M : HomologicalComplex D s)
  (e : (F.mapHomologicalComplex s).obj K ≅ L)
  (d : (G.mapHomologicalComplex s).obj L ≅ M)
  (h : ((F ⋙ G).mapHomologicalComplex s).obj K ≅ M)
  (eh : (G.mapHomologicalComplex s).map e.hom ≫ d.hom = h.hom)
  (q : ι)

include eh in
theorem comparison :
    G.map (HomologySquare.iso F e q).hom ≫
      (HomologySquare.iso G d q).hom =
    (HomologySquare.iso (F ⋙ G) h q).hom := by
  have hn := ShortComplex.mapHomologyIso_inv_naturality
    ((shortComplexFunctor B s q).map e.hom) G
  change G.map (homologyMap e.hom q) ≫ ((L.sc q).mapHomologyIso G).inv =
    ((((F.mapHomologicalComplex s).obj K).sc q).mapHomologyIso G).inv ≫
      homologyMap ((G.mapHomologicalComplex s).map e.hom) q at hn
  simp only [HomologySquare.iso, Iso.trans_hom, Iso.symm_hom,
    homologyMapIso_hom, G.map_comp, Category.assoc]
  rw [← Category.assoc (G.map (homologyMap e.hom q)), hn]
  simp only [Category.assoc]
  rw [← homologyMap_comp, eh, MapHomologyIsoCompose.inv_comp]
  simp only [Category.assoc]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.HomologyComposition
