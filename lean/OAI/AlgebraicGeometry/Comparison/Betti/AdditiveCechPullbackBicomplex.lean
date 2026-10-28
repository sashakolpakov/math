import OAI.AlgebraicGeometry.Comparison.Betti.Cech.PullbackNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Cech.FunctorAdditive

/-! # Additive Cech Pullback Bicomplex -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechPullbackBicomplex

noncomputable section

/-! The original pullback of Čech cochains acts functorially on coefficient complexes. -/

open _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : TopCat.{0}} (f : Y ⟶ X) {ι : Type} (U : ι → Opens X)

abbrev additivePresheafDirectImage :
    ((Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}) ⥤ ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}) :=
  (Functor.whiskeringLeft (Opens X)ᵒᵖ (Opens Y)ᵒᵖ AddCommGrpCat.{0}).obj (Opens.map f).op

instance additivePresheafDirectImage_additive : (additivePresheafDirectImage f).Additive where
  map_add := by intros; rfl

def additiveCechDirectImageFunctorIso :
    additivePresheafDirectImage f ⋙ cechComplexFunctor U ≅
      cechComplexFunctor (fun i => (Opens.map f).obj (U i)) :=
  NatIso.ofComponents (fun P => AdditiveCechImage.additiveCechDirectImageIso f U P)
    (fun α => AdditiveCechImage.additiveCechDirectImageIso_naturality f U α)

def nativeAdditiveCechBicomplex (K : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}) ℕ) :
    HomologicalComplex₂ AddCommGrpCat.{0} (.up ℕ) (.up ℕ) :=
  ((cechComplexFunctor U).mapHomologicalComplex (.up ℕ)).obj K

variable {K : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}) ℕ}
    {L : CochainComplex ((Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}) ℕ}
    (α : K ⟶ ((additivePresheafDirectImage f).mapHomologicalComplex (.up ℕ)).obj L)

def additiveCechPullbackBicomplexMap : nativeAdditiveCechBicomplex U K ⟶
    nativeAdditiveCechBicomplex (fun i => (Opens.map f).obj (U i)) L :=
  ((cechComplexFunctor U).mapHomologicalComplex (.up ℕ)).map α ≫
    (NatIso.mapHomologicalComplex (additiveCechDirectImageFunctorIso f U) (.up ℕ)).hom.app L

theorem additiveCechPullbackBicomplexMap_f (r : ℕ) :
    (additiveCechPullbackBicomplexMap f U α).f r =
      (cechComplexFunctor U).map (α.f r) ≫ (AdditiveCechImage.additiveCechDirectImageIso f U (L.X r)).hom := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechPullbackBicomplex
