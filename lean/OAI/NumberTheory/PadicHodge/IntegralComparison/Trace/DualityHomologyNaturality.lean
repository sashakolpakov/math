import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.DualityHomology

/-! # Duality Homology Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.DualityHomologyNaturality

noncomputable section

/-! The trace duality on homology is contravariantly natural in the
original chain complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false

universe u v

open OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.DualityHomology

variable {C : Type v} [Category.{u} C] [Preadditive C]
  (R : Type u) [CommRing R] [Module.Injective R R]
  (F : C ⥤ ModuleCat.{u} R) [F.Additive]
  {ω : C} (τ : F.obj ω ⟶ ModuleCat.of R R)
  {P Q : ChainComplex C ℕ} (a : P ⟶ Q)

def homMap : DualityHomology.homComplex (ω := ω) Q ⟶ DualityHomology.homComplex (ω := ω) P :=
  ((preadditiveYoneda.obj ω).mapHomologicalComplex (.up ℕ)).map
    ((HomologicalComplex.opFunctor C (.down ℕ)).map a.op)

def coefficientMap : DualityHomology.coefficientComplex R F P ⟶ DualityHomology.coefficientComplex R F Q :=
  (F.mapHomologicalComplex (.down ℕ)).map a

@[reassoc]
theorem naturality
    (hP : ∀ i, Function.Bijective (DualityDescent.pairingMap F τ (P.X i)))
    (hQ : ∀ i, Function.Bijective (DualityDescent.pairingMap F τ (Q.X i)))
    (n : ℕ) :
    HomologicalComplex.homologyMap (homMap (ω := ω) a) n ≫ (DualityHomology.homologyIso R F τ P hP n).hom =
      (DualityHomology.homologyIso R F τ Q hQ n).hom ≫
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat).map
          (ModuleCat.ofHom (HomologicalComplex.homologyMap (coefficientMap R F a) n).hom.dualMap) := by
  let aop := (HomologicalComplex.opFunctor C (.down ℕ)).map a.op
  let G := forget₂ (ModuleCat.{u} R) AddCommGrpCat
  let b := DualComplexHomology.map R (coefficientMap R F a)
  have hc := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (((DualityComplex.pairing R F τ).mapHomologicalComplex (.up ℕ)).naturality aop)
  simp only [HomologicalComplex.homologyMap_comp] at hc
  have hf :
      HomologicalComplex.homologyMap ((G.mapHomologicalComplex (ComplexShape.down ℕ).symm).map b) n ≫
          (((DualComplexHomology.complex R (DualityHomology.coefficientComplex R F P)).sc n).mapHomologyIso G).hom =
        (((DualComplexHomology.complex R (DualityHomology.coefficientComplex R F Q)).sc n).mapHomologyIso G).hom ≫
          G.map (HomologicalComplex.homologyMap b n) :=
    ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ).symm n).map b) G
  have hd := DualComplexHomology.map_square G _ _ _ _
    (DualComplexHomology.naturality R (coefficientMap R F a) n)
  have hfhd := DualComplexHomology.compose_squares _ _ _ _ _ _ _ hf hd
  simpa only [DualityHomology.homologyIso, Iso.trans_hom, Functor.mapIso_hom,
    HomologicalComplex.homologyMapIso_hom, DualityComplex.complexIso_hom,
    DualityComplex.complexMap, aop, G, homMap,
    HomologicalComplex.opFunctor, Category.assoc] using
      DualComplexHomology.compose_squares _ _ _ _ _ _ _ hc hfhd

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.DualityHomologyNaturality
