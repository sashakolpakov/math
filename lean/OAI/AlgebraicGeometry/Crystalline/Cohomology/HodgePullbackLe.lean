import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo
import OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeTruncationTerm
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ShiftedPullback
import OAI.AlgebraicGeometry.Crystalline.Cohomology.NaturalPullback

/-! # Hodge Pullback Le -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgePullbackLe.HodgePullback

noncomputable section

/-!
# Pullback preserves the native Hodge filtration

The actual inverse image of the truncated de Rham complex factors through
the same degree truncation of the target. Passing this factorization to
the derived category proves preservation of Cohomology's native image filtration.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo.DeRhamPullback

universe u

variable {R : Type u} [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)

def truncatedSheafPullback (j : ℤ) :
    ((DeRhamPullbackTo.DeRhamPullback.inverseImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (HodgeFiltrationD.HodgeFiltration.brutal (DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) j) ⟶
        HodgeFiltrationD.HodgeFiltration.brutal (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) j :=
  HodgeTruncationTerm.HodgeTruncationFactor.mappedFactor j (DeRhamPullbackTo.DeRhamPullback.inverseImage f) (DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) (DeRhamPullbackTo.DeRhamPullback.sheafPullback f)

theorem truncatedSheafPullback_inclusion (j : ℤ) :
    truncatedSheafPullback f j ≫ HodgeFiltrationD.HodgeFiltration.inclusion (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) j =
      ((DeRhamPullbackTo.DeRhamPullback.inverseImage f).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (HodgeFiltrationD.HodgeFiltration.inclusion (DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) j) ≫ DeRhamPullbackTo.DeRhamPullback.sheafPullback f :=
  HodgeTruncationTerm.HodgeTruncationFactor.mappedFactor_inclusion j (DeRhamPullbackTo.DeRhamPullback.inverseImage f) (DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) (DeRhamPullbackTo.DeRhamPullback.sheafPullback f)

def truncatedSheafPullbackInt (j : ℤ) :
    ((DeRhamPullbackTo.DeRhamPullback.inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((HodgeFiltrationD.HodgeFiltration.brutal (DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) j).extend ComplexShape.embeddingUpNat) ⟶
        (HodgeFiltrationD.HodgeFiltration.brutal (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) j).extend ComplexShape.embeddingUpNat :=
  (Comparison.Betti.Complex.Extension.mapExtendIso (DeRhamPullbackTo.DeRhamPullback.inverseImage f) ComplexShape.embeddingUpNat
    (HodgeFiltrationD.HodgeFiltration.brutal (DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) j)).hom ≫
      HomologicalComplex.extendMap (truncatedSheafPullback f j) ComplexShape.embeddingUpNat

theorem truncatedSheafPullbackInt_inclusion (j : ℤ) :
    truncatedSheafPullbackInt f j ≫
      HomologicalComplex.extendMap (HodgeFiltrationD.HodgeFiltration.inclusion (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) j) ComplexShape.embeddingUpNat =
    ((DeRhamPullbackTo.DeRhamPullback.inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap (HodgeFiltrationD.HodgeFiltration.inclusion (DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) j) ComplexShape.embeddingUpNat) ≫
        DeRhamPullbackTo.DeRhamPullback.sheafPullbackInt f := by
  unfold truncatedSheafPullbackInt DeRhamPullbackTo.DeRhamPullback.sheafPullbackInt
  rw [Category.assoc, ← HomologicalComplex.extendMap_comp, truncatedSheafPullback_inclusion,
    HomologicalComplex.extendMap_comp, ← Category.assoc,
    ← Comparison.Betti.Complex.Extension.mapExtendIso_naturality]
  exact Category.assoc _ _ _

def derivedTruncatedPullback (j : ℤ) :
    (DeRhamPullbackTo.DeRhamPullback.derivedInverseImage f).obj ((HodgeFiltrationD.HodgeFiltration.derivedFunctor R Y).obj
      (HodgeFiltrationD.HodgeFiltration.brutal (DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) j)) ⟶
        (HodgeFiltrationD.HodgeFiltration.derivedFunctor R X).obj (HodgeFiltrationD.HodgeFiltration.brutal (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) j) :=
  (DeRhamPullbackTo.DeRhamPullback.inverseImage f).mapDerivedCategoryFactors.hom.app
    ((HodgeFiltrationD.HodgeFiltration.brutal (DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) j).extend ComplexShape.embeddingUpNat) ≫
      DerivedCategory.Q.map (truncatedSheafPullbackInt f j)

theorem derivedTruncatedPullback_inclusion (j : ℤ) :
    derivedTruncatedPullback f j ≫
      (HodgeFiltrationD.HodgeFiltration.derivedFunctor R X).map (HodgeFiltrationD.HodgeFiltration.inclusion (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) j) =
    (DeRhamPullbackTo.DeRhamPullback.derivedInverseImage f).map
      ((HodgeFiltrationD.HodgeFiltration.derivedFunctor R Y).map (HodgeFiltrationD.HodgeFiltration.inclusion (DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) j)) ≫
        DeRhamPullbackTo.DeRhamPullback.derivedPullback f := by
  let iY : (HodgeFiltrationD.HodgeFiltration.brutal (DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) j).extend ComplexShape.embeddingUpNat ⟶
      DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R Y := HomologicalComplex.extendMap
        (HodgeFiltrationD.HodgeFiltration.inclusion (DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) j) ComplexShape.embeddingUpNat
  let iX : (HodgeFiltrationD.HodgeFiltration.brutal (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) j).extend ComplexShape.embeddingUpNat ⟶
      DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R X := HomologicalComplex.extendMap
        (HodgeFiltrationD.HodgeFiltration.inclusion (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) j) ComplexShape.embeddingUpNat
  exact NaturalPullback.NaturalPullbackFactor.factor ((DeRhamPullbackTo.DeRhamPullback.inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ))
    DerivedCategory.Q DerivedCategory.Q (DeRhamPullbackTo.DeRhamPullback.derivedInverseImage f)
    (DeRhamPullbackTo.DeRhamPullback.inverseImage f).mapDerivedCategoryFactors.hom iY iX (DeRhamPullbackTo.DeRhamPullback.sheafPullbackInt f)
    (truncatedSheafPullbackInt f j) (truncatedSheafPullbackInt_inclusion f j)

def truncatedPullback (n : ℕ) (j : ℤ) :
    ShiftedHom ((DerivedCategory.singleFunctor (DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) 0).obj (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y))
      ((HodgeFiltrationD.HodgeFiltration.derivedFunctor R Y).obj (HodgeFiltrationD.HodgeFiltration.brutal (DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) j)) (n : ℤ) →
    ShiftedHom ((DerivedCategory.singleFunctor (DeRhamGlobalId.DeRhamGlobal.Sheaves R X) 0).obj (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X))
      ((HodgeFiltrationD.HodgeFiltration.derivedFunctor R X).obj (HodgeFiltrationD.HodgeFiltration.brutal (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) j)) (n : ℤ) :=
  fun a => (DeRhamPullbackTo.DeRhamPullback.derivedConstantIso f).inv ≫ (DeRhamPullbackTo.DeRhamPullback.derivedInverseImage f).map a ≫
    ((DeRhamPullbackTo.DeRhamPullback.derivedInverseImage f).commShiftIso (n : ℤ)).hom.app
      ((HodgeFiltrationD.HodgeFiltration.derivedFunctor R Y).obj (HodgeFiltrationD.HodgeFiltration.brutal (DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) j)) ≫
        (shiftFunctor (DerivedCategory (DeRhamGlobalId.DeRhamGlobal.Sheaves R X)) (n : ℤ)).map (derivedTruncatedPullback f j)

theorem filtrationMap_pullback (n : ℕ) (j : ℤ)
    (a : ShiftedHom ((DerivedCategory.singleFunctor (DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) 0).obj (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y))
      ((HodgeFiltrationD.HodgeFiltration.derivedFunctor R Y).obj (HodgeFiltrationD.HodgeFiltration.brutal (DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) j)) (n : ℤ)) :
    DeRhamPullbackTo.DeRhamPullback.pullback f n (HodgeFiltrationD.HodgeFiltration.filtrationMap R Y n j a) =
      HodgeFiltrationD.HodgeFiltration.filtrationMap R X n j (truncatedPullback f n j a) := by
  let iY := (HodgeFiltrationD.HodgeFiltration.derivedFunctor R Y).map (HodgeFiltrationD.HodgeFiltration.inclusion (DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) j)
  let iX := (HodgeFiltrationD.HodgeFiltration.derivedFunctor R X).map (HodgeFiltrationD.HodgeFiltration.inclusion (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) j)
  let pFull : (DeRhamPullbackTo.DeRhamPullback.derivedInverseImage f).obj ((HodgeFiltrationD.HodgeFiltration.derivedFunctor R Y).obj (DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y)) ⟶
      (HodgeFiltrationD.HodgeFiltration.derivedFunctor R X).obj (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) := DeRhamPullbackTo.DeRhamPullback.derivedPullback f
  have hp : derivedTruncatedPullback f j ≫ iX = (DeRhamPullbackTo.DeRhamPullback.derivedInverseImage f).map iY ≫ pFull :=
    derivedTruncatedPullback_inclusion f j
  have he := ShiftedPullback.ShiftedPullbackFactor.factor (DeRhamPullbackTo.DeRhamPullback.derivedInverseImage f) iY iX pFull
    (derivedTruncatedPullback f j) hp (n : ℤ) a
  have he' := congrArg (fun z => (DeRhamPullbackTo.DeRhamPullback.derivedConstantIso f).inv ≫ z) he
  change (DeRhamPullbackTo.DeRhamPullback.derivedConstantIso f).inv ≫ ((DeRhamPullbackTo.DeRhamPullback.derivedInverseImage f).map
      (a ≫ (shiftFunctor (DerivedCategory (DeRhamGlobalId.DeRhamGlobal.Sheaves R Y)) (n : ℤ)).map iY) ≫
      ((DeRhamPullbackTo.DeRhamPullback.derivedInverseImage f).commShiftIso (n : ℤ)).hom.app _ ≫
      (shiftFunctor (DerivedCategory (DeRhamGlobalId.DeRhamGlobal.Sheaves R X)) (n : ℤ)).map pFull) =
    ((DeRhamPullbackTo.DeRhamPullback.derivedConstantIso f).inv ≫ (DeRhamPullbackTo.DeRhamPullback.derivedInverseImage f).map a ≫
      ((DeRhamPullbackTo.DeRhamPullback.derivedInverseImage f).commShiftIso (n : ℤ)).hom.app _ ≫
      (shiftFunctor (DerivedCategory (DeRhamGlobalId.DeRhamGlobal.Sheaves R X)) (n : ℤ)).map (derivedTruncatedPullback f j)) ≫
      (shiftFunctor (DerivedCategory (DeRhamGlobalId.DeRhamGlobal.Sheaves R X)) (n : ℤ)).map iX
  exact he'.trans (Category.assoc _ _ _).symm

/-- Every scheme morphism preserves the actual degree-image Hodge filtration. -/
theorem filtration_map_le (n : ℕ) (j : ℤ) :
    (HodgeFiltrationD.HodgeFiltration.filtration R Y n j).map (DeRhamPullbackTo.DeRhamPullback.pullback f n) ≤ HodgeFiltrationD.HodgeFiltration.filtration R X n j := by
  rintro _ ⟨a, ⟨b, rfl⟩, rfl⟩
  exact ⟨truncatedPullback f n j b, (filtrationMap_pullback f n j b).symm⟩

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgePullbackLe.HodgePullback
