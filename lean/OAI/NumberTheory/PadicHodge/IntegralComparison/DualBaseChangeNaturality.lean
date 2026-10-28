import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FreeDualBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DualFlatBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ResolutionOrientation

/-! # Dual Base Change Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DualBaseChangeNaturality

noncomputable section

/-! Naturality of the actual finite-free dual complex and its homology
under flat scalar extension and an identified scalar-extended complex. -/

open _root_.CategoryTheory _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

abbrev tensorFunctor := Koszul.FlatBaseChange.tensorFunctor R S
abbrev tensorComplex := (tensorFunctor R S).mapHomologicalComplex (.down ℕ)
abbrev tensorDualComplex := (tensorFunctor R S).mapHomologicalComplex (.up ℕ)

variable {K L : ChainComplex (ModuleCat.{u} R) ℕ}
  [∀ i, Module.Free R (K.X i)] [∀ i, Module.Finite R (K.X i)]
  [∀ i, Module.Free R (L.X i)] [∀ i, Module.Finite R (L.X i)]

theorem complexIso_naturality (f : K ⟶ L) :
    (tensorDualComplex R S).map (DualComplexHomology.map R f) ≫
        (IntegralComparison.Finite.FreeDualBaseChange.complexIso R S K).hom =
      (IntegralComparison.Finite.FreeDualBaseChange.complexIso R S L).hom ≫
        DualComplexHomology.map S ((tensorComplex R S).map f) := by
  apply Hom.ext
  funext i
  exact ModuleCat.hom_ext (IntegralComparison.Finite.FreeDualBaseChange.naturality R S (f.f i).hom)

def iso (K' : ChainComplex (ModuleCat.{u} S) ℕ)
    (e : (tensorComplex R S).obj K ≅ K') :
    (tensorDualComplex R S).obj (DualComplexHomology.complex R K) ≅
      DualComplexHomology.complex S K' :=
  IntegralComparison.Finite.FreeDualBaseChange.complexIso R S K ≪≫ Koszul.DualFlatBaseChange.dualIso S e

theorem iso_naturality {K' L' : ChainComplex (ModuleCat.{u} S) ℕ}
    (eK : (tensorComplex R S).obj K ≅ K') (eL : (tensorComplex R S).obj L ≅ L')
    (f : K ⟶ L) (g : K' ⟶ L')
    (h : eK.hom ≫ g = (tensorComplex R S).map f ≫ eL.hom) :
    (tensorDualComplex R S).map (DualComplexHomology.map R f) ≫
        (iso R S K' eK).hom =
      (iso R S L' eL).hom ≫ DualComplexHomology.map S g := by
  have he : eK.inv ≫ (tensorComplex R S).map f = g ≫ eL.inv := by
    apply (cancel_epi eK.hom).mp
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
      ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change _ ≫ ((IntegralComparison.Finite.FreeDualBaseChange.complexIso R S K).hom ≫
      DualComplexHomology.map S eK.inv) =
    ((IntegralComparison.Finite.FreeDualBaseChange.complexIso R S L).hom ≫
      DualComplexHomology.map S eL.inv) ≫ DualComplexHomology.map S g
  rw [← Category.assoc, complexIso_naturality, Category.assoc,
    ← Koszul.ResolutionOrientation.dual_map_comp, he,
    Koszul.ResolutionOrientation.dual_map_comp, ← Category.assoc]

variable [Module.Flat R S]

def homologyIso (K' : ChainComplex (ModuleCat.{u} S) ℕ)
    (e : (tensorComplex R S).obj K ≅ K') (i : ℕ) :
    (tensorFunctor R S).obj ((DualComplexHomology.complex R K).homology i) ≅
      (DualComplexHomology.complex S K').homology i :=
  (((DualComplexHomology.complex R K).sc i).mapHomologyIso (tensorFunctor R S)).symm ≪≫
    homologyMapIso (iso R S K' e) i

theorem homologyIso_naturality {K' L' : ChainComplex (ModuleCat.{u} S) ℕ}
    (eK : (tensorComplex R S).obj K ≅ K') (eL : (tensorComplex R S).obj L ≅ L')
    (f : K ⟶ L) (g : K' ⟶ L')
    (h : eK.hom ≫ g = (tensorComplex R S).map f ≫ eL.hom) (i : ℕ) :
    (tensorFunctor R S).map (homologyMap (DualComplexHomology.map R f) i) ≫
        (homologyIso R S K' eK i).hom =
      (homologyIso R S L' eL i).hom ≫ homologyMap (DualComplexHomology.map S g) i := by
  have h₁ := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (.up ℕ) i).map
      (DualComplexHomology.map R f)) (tensorFunctor R S)
  have h₂ := congrArg (fun a => homologyMap a i) (iso_naturality R S eK eL f g h)
  simp only [homologyMap_comp] at h₂
  change (tensorFunctor R S).map (homologyMap (DualComplexHomology.map R f) i) ≫
      (((DualComplexHomology.complex R K).sc i).mapHomologyIso (tensorFunctor R S)).inv =
    (((DualComplexHomology.complex R L).sc i).mapHomologyIso (tensorFunctor R S)).inv ≫
      homologyMap ((tensorDualComplex R S).map (DualComplexHomology.map R f)) i at h₁
  dsimp only [homologyIso, Iso.trans_hom, Iso.symm_hom, homologyMapIso_hom]
  exact DualComplexHomology.compose_squares _ _ _ _ _ _ _ h₁ h₂

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DualBaseChangeNaturality
