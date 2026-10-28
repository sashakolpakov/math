import OAI.NumberTheory.PadicHodge.GeometricComparison.TruncatedFunctorIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.AdapterNaturality

/-! # Filtration Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.FiltrationPullback

noncomputable section

/-! Native algebraic de Rham pullback preserves the filtration defined by degree truncation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

variable {R : Type} [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)

abbrev truncatedComplex (X : Over (Spec (CommRingCat.of R))) (r : ℤ) :=
  AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r

def truncatedSheafPullback (r : ℤ) :
    ((Int.inverseImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj (truncatedComplex Y r) ⟶
      truncatedComplex X r :=
  TruncatedFunctorIso.TruncatedPullback.map (Int.inverseImage f) (Int.sheafPullback f) r

def integerInclusion (X : Over (Spec (CommRingCat.of R))) (r : ℤ) :
    (truncatedComplex X r).extend ComplexShape.embeddingUpNat ⟶ AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R X :=
  HomologicalComplex.extendMap (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r) ComplexShape.embeddingUpNat

def truncatedSheafPullbackInt (r : ℤ) :
    ((Int.inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((truncatedComplex Y r).extend ComplexShape.embeddingUpNat) ⟶
        (truncatedComplex X r).extend ComplexShape.embeddingUpNat :=
  Intrinsic.ExtensionAdapter.FormsAdapter.extendedPullback (Int.inverseImage f) ComplexShape.embeddingUpNat (truncatedSheafPullback f r)

theorem integerInclusion_square (r : ℤ) :
    ((Int.inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).map (integerInclusion Y r) ≫
        Int.sheafPullbackInt f = truncatedSheafPullbackInt f r ≫ integerInclusion X r :=
  Intrinsic.ExtensionAdapter.FormsAdapter.extendedPullback_square (Int.inverseImage f) ComplexShape.embeddingUpNat
    (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) r) (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r)
    (truncatedSheafPullback f r) (Int.sheafPullback f)
    (TruncatedFunctorIso.TruncatedPullback.inclusion_square (Int.inverseImage f) (Int.sheafPullback f) r).symm

def derivedInclusion (X : Over (Spec (CommRingCat.of R))) (r : ℤ) :
    DerivedCategory.Q.obj ((truncatedComplex X r).extend ComplexShape.embeddingUpNat) ⟶
      DerivedCategory.Q.obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R X) :=
  DerivedCategory.Q.map (integerInclusion X r)

def truncatedDerivedPullback (r : ℤ) :
    (Int.derivedInverseImage f).obj
      (DerivedCategory.Q.obj ((truncatedComplex Y r).extend ComplexShape.embeddingUpNat)) ⟶
        DerivedCategory.Q.obj ((truncatedComplex X r).extend ComplexShape.embeddingUpNat) :=
  (Int.inverseImage f).mapDerivedCategoryFactors.hom.app
    ((truncatedComplex Y r).extend ComplexShape.embeddingUpNat) ≫
      DerivedCategory.Q.map (truncatedSheafPullbackInt f r)

theorem derivedInclusion_square (r : ℤ) :
    (Int.derivedInverseImage f).map (derivedInclusion Y r) ≫ Int.derivedPullback f =
      truncatedDerivedPullback f r ≫ derivedInclusion X r := by
  have h := (Int.inverseImage f).mapDerivedCategoryFactors.hom.naturality (integerInclusion Y r)
  have h₂ := AdapterNaturality.FormsAdapter.map_commuting_square DerivedCategory.Q (integerInclusion_square f r)
  exact SheafAdapterNaturality.FormsAdapter.composition_square h h₂

abbrev TruncatedCohomology (X : Over (Spec (CommRingCat.of R))) (n : ℕ) (r : ℤ) :=
  ((DerivedCategory.singleFunctor (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) 0).obj
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)) ⟶
      (DerivedCategory.Q.obj ((truncatedComplex X r).extend ComplexShape.embeddingUpNat))⟦(n : ℤ)⟧

def truncatedPullback (n : ℕ) (r : ℤ) : TruncatedCohomology Y n r →ₗ[R] TruncatedCohomology X n r where
  toFun α := (Int.derivedConstantIso f).inv ≫ (Int.derivedInverseImage f).map α ≫
    ((Int.derivedInverseImage f).commShiftIso (n : ℤ)).hom.app
      (DerivedCategory.Q.obj ((truncatedComplex Y r).extend ComplexShape.embeddingUpNat)) ≫
        (shiftFunctor (DerivedCategory (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X)) (n : ℤ)).map
          (truncatedDerivedPullback f r)
  map_add' _ _ := by simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
  map_smul' _ _ := by simp only [Functor.map_smul, Linear.comp_smul, Linear.smul_comp, RingHom.id_apply]

theorem filtrationMap_pullback (n : ℕ) (r : ℤ) (x : TruncatedCohomology Y n r) :
    Int.pullback f n (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtrationMap R Y n r x) =
      AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtrationMap R X n r (truncatedPullback f n r x) := by
  let S := shiftFunctor (DerivedCategory (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X)) (n : ℤ)
  have hshift := ((Int.derivedInverseImage f).commShiftIso (n : ℤ)).hom.naturality (derivedInclusion Y r)
  have hmap := AdapterNaturality.FormsAdapter.map_commuting_square S (derivedInclusion_square f r)
  have ht := (SheafAdapterNaturality.FormsAdapter.composition_square hshift hmap).trans (Category.assoc _ _ _)
  change (Int.derivedConstantIso f).inv ≫
      (Int.derivedInverseImage f).map (x ≫
        (shiftFunctor (DerivedCategory (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y)) (n : ℤ)).map (derivedInclusion Y r)) ≫
      ((Int.derivedInverseImage f).commShiftIso (n : ℤ)).hom.app
        (DerivedCategory.Q.obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R Y)) ≫ S.map (Int.derivedPullback f) =
    ((Int.derivedConstantIso f).inv ≫ (Int.derivedInverseImage f).map x ≫
      ((Int.derivedInverseImage f).commShiftIso (n : ℤ)).hom.app
        (DerivedCategory.Q.obj ((truncatedComplex Y r).extend ComplexShape.embeddingUpNat)) ≫
      S.map (truncatedDerivedPullback f r)) ≫ S.map (derivedInclusion X r)
  erw [(Int.derivedInverseImage f).map_comp]
  simp only [Category.assoc]
  exact congrArg (fun k => (Int.derivedConstantIso f).inv ≫ (Int.derivedInverseImage f).map x ≫ k) ht

/-- Functorial preservation of every native Hodge-filtration step. -/
theorem filtration_pullback (n : ℕ) (r : ℤ) :
    (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration R Y n r).map (Int.pullback f n) ≤ AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration R X n r := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact ⟨truncatedPullback f n r x, (filtrationMap_pullback f n r x).symm⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.FiltrationPullback
