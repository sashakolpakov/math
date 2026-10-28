import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.DualityComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.DualHomologyTransport
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Duality Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.DualityHomology

noncomputable section

/-! A termwise perfect trace pairing identifies the homology of the
representable Hom complex with the dual of the homology of the mapped
chain complex. All coefficient and complex transports are performed
before specializing to geometric sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false

universe u v

variable {C : Type v} [Category.{u} C] [Preadditive C]
  (R : Type u) [CommRing R] [Module.Injective R R]
  (F : C ⥤ ModuleCat.{u} R) [F.Additive]
  {ω : C} (τ : F.obj ω ⟶ ModuleCat.of R R)

def homComplex (P : ChainComplex C ℕ) : CochainComplex AddCommGrpCat.{u} ℕ :=
  ((preadditiveYoneda.obj ω).mapHomologicalComplex (.up ℕ)).obj P.op

def coefficientComplex (P : ChainComplex C ℕ) : ChainComplex (ModuleCat.{u} R) ℕ :=
  (F.mapHomologicalComplex (.down ℕ)).obj P

def homologyIso (P : ChainComplex C ℕ)
    (hP : ∀ i, Function.Bijective (DualityDescent.pairingMap F τ (P.X i)))
    (n : ℕ) : (homComplex (ω := ω) P).homology n ≅
      DualHomologyTransport.dualGroup R ((coefficientComplex R F P).homology n) :=
  HomologicalComplex.homologyMapIso
      (DualityComplex.complexIso R F τ (.up ℕ) P.op hP) n ≪≫
    ((DualComplexHomology.complex R (coefficientComplex R F P)).sc n).mapHomologyIso
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat) ≪≫
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat).mapIso
      (DualComplexHomology.homologyIso R (coefficientComplex R F P) n)

def homologyIsoTo (P : ChainComplex C ℕ)
    (hP : ∀ i, Function.Bijective (DualityDescent.pairingMap F τ (P.X i)))
    (n : ℕ) {D : ModuleCat.{u} R} (e : (coefficientComplex R F P).homology n ≅ D) :
    (homComplex (ω := ω) P).homology n ≅ DualHomologyTransport.dualGroup R D :=
  DualHomologyTransport.transport R (homologyIso R F τ P hP n) e

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.DualityHomology
