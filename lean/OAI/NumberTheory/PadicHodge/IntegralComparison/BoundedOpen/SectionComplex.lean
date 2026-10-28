import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionPresheaf

/-! # Section Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex

noncomputable section

/-!
# IntegralComparison: an open-section complex computing the original bounded crystalline cohomology locally
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)

def functor : BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fY n ⥤
    (Y.Opensᵒᵖ ⥤ ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := B))) :=
  SectionPresheaf.functor fY n ⋙
    (Functor.whiskeringRight Y.Opensᵒᵖ (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))
      (ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := B)))).obj (ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))

instance functor_additive : (functor (p := p) (J := J) (δ := δ) fY n).Additive := by
  dsimp only [functor]
  infer_instance

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
  (p := p) (J := J) (δ := δ) fY n))

def complex : CochainComplex (Y.Opensᵒᵖ ⥤ ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := B))) ℕ :=
  ((functor fY n).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex

def evaluation (V : Y.Opens) : (Y.Opensᵒᵖ ⥤ ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := B))) ⥤
    ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := B)) :=
  (CategoryTheory.evaluation Y.Opensᵒᵖ (ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := B)))).obj (op V)

instance evaluation_additive (V : Y.Opens) : (SectionComplex.evaluation (B := B) V).Additive := by
  dsimp only [SectionComplex.evaluation]
  infer_instance

def evaluationIso (V : Y.Opens) :
    ((SectionComplex.evaluation (B := B) V).mapHomologicalComplex (ComplexShape.up ℕ)).obj (complex fY n I) ≅
      Resolution.complex fY V.ι n I := Iso.refl _

def homologyIso (V : Y.Opens) (i : ℕ) :
    (((SectionComplex.evaluation (B := B) V).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (complex fY n I)).homology i ≅
      ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.CrystallineCohomology.Cohomology
        (p := p) (J := J) (δ := δ) (V.ι ≫ fY) n i) :=
  (HomologicalComplex.homologyFunctor _ _ i).mapIso (evaluationIso fY n I V) ≪≫
    Resolution.homologyIso V.ι n I rfl i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex
