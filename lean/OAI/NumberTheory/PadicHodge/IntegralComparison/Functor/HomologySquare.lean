import OAI.NumberTheory.PadicHodge.IntegralComparison.DualComplexHomology

/-! # Homology Square -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.HomologySquare

noncomputable section

/-! A commuting square of complexes gives the corresponding commuting
square for canonical exact-functor homology comparisons. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
  {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex C c} {K' L' : HomologicalComplex D c}

def iso (e : (F.mapHomologicalComplex c).obj K ≅ K') (i : ι) :
    F.obj (K.homology i) ≅ K'.homology i :=
  ((K.sc i).mapHomologyIso F).symm ≪≫ homologyMapIso e i

theorem naturality (a : K ⟶ L) (b : K' ⟶ L')
    (eK : (F.mapHomologicalComplex c).obj K ≅ K')
    (eL : (F.mapHomologicalComplex c).obj L ≅ L')
    (h : (F.mapHomologicalComplex c).map a ≫ eL.hom = eK.hom ≫ b) (i : ι) :
    F.map (homologyMap a i) ≫ (iso F eL i).hom =
      (iso F eK i).hom ≫ homologyMap b i := by
  have h₁ := ShortComplex.mapHomologyIso_inv_naturality
    ((shortComplexFunctor C c i).map a) F
  change F.map (homologyMap a i) ≫ ((L.sc i).mapHomologyIso F).inv =
    ((K.sc i).mapHomologyIso F).inv ≫ homologyMap ((F.mapHomologicalComplex c).map a) i at h₁
  have h₂ := congrArg (fun f => homologyMap f i) h
  simp only [homologyMap_comp] at h₂
  exact DualComplexHomology.compose_squares _ _ _ _ _ _ _ h₁ h₂

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.HomologySquare
