import OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi

/-! # Complex Assembly Trans -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyTrans.ComplexAssemblyTransport

/-! # Assembly commutes with restriction of objects and change of coefficients -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C D V W : Type*} [Category C] [Category D] [Category V] [Category W]
  [HasZeroMorphisms V] [HasZeroMorphisms W]
  (F : C ⥤ D) (R : V ⥤ W) [R.PreservesZeroMorphisms]

def transport : (D ⥤ V) ⥤ (C ⥤ W) :=
  (Functor.whiskeringLeft C D V).obj F ⋙ (Functor.whiskeringRight C V W).obj R

instance transport_preservesZeroMorphisms : (transport F R).PreservesZeroMorphisms where
  map_zero _ _ := by
    apply NatTrans.ext
    funext c
    exact R.map_zero _ _

def iso {ι : Type*} (c : ComplexShape ι) (K : D ⥤ HomologicalComplex V c) :
    ((transport F R).mapHomologicalComplex c).obj (ComplexAssemblyQuasi.ComplexAssembly.complex c K) ≅
      ComplexAssemblyQuasi.ComplexAssembly.complex c (F ⋙ K ⋙ R.mapHomologicalComplex c) :=
  Iso.refl _

theorem iso_trans_component {ι : Type*} (c : ComplexShape ι)
    (K : D ⥤ HomologicalComplex V c) (K' : C ⥤ HomologicalComplex W c)
    (e : F ⋙ K ⋙ R.mapHomologicalComplex c ≅ K') (i : ι) (x : C) :
    (((iso F R c K ≪≫ (ComplexAssemblyQuasi.ComplexAssembly.functor c).mapIso e).hom.f i).app x) =
      (e.hom.app x).f i := by
  change 𝟙 _ ≫ (e.hom.app x).f i = (e.hom.app x).f i
  exact Category.id_comp _

end AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyTrans.ComplexAssemblyTransport

namespace AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyTrans.ComplexAssemblyConjugation

/-! # Components of a conjugated complex map after object and coefficient restriction -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C D V W : Type*} [Category C] [Category D] [Category V] [Category W]
  [HasZeroMorphisms V] [HasZeroMorphisms W]
  (F : C ⥤ D) (R : V ⥤ W) [R.PreservesZeroMorphisms]
  {ι : Type*} (c : ComplexShape ι)
  {K K' : HomologicalComplex (D ⥤ V) c}
  {L L' : HomologicalComplex (C ⥤ W) c}
  (a : K ≅ K')
  (b : ((ComplexAssemblyTransport.transport F R).mapHomologicalComplex c).obj K' ≅ L')
  (d : L ≅ L')

theorem component (j : ι) (Q : C) :
    (((((ComplexAssemblyTransport.transport F R).mapHomologicalComplex c).mapIso a ≪≫ b ≪≫ d.symm).hom.f j).app Q) =
      R.map ((a.hom.f j).app (F.obj Q)) ≫ (b.hom.f j).app Q ≫ (d.inv.f j).app Q := rfl

end AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyTrans.ComplexAssemblyConjugation

end

end OAI
