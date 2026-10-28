import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.IsoEq
import OAI.NumberTheory.PadicHodge.GeometricComparison.DerivedEquivalenceIs

/-! # Iso Cohomology -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.IsoCohomology

noncomputable section

/-! Scheme isomorphisms induce equivalences through the native de Rham pullback construction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal

variable {R : Type} [CommRing R] {X Y : Over (Spec (CommRingCat.of R))}
  (f : X ⟶ Y) [IsIso f]

instance inverseImageComplex_isEquivalence :
    ((Int.inverseImage f).mapHomologicalComplex (ComplexShape.up ℕ)).IsEquivalence := by
  let e := (Int.inverseImage f).asEquivalence
  let : e.functor.PreservesZeroMorphisms := inferInstanceAs (Int.inverseImage f).PreservesZeroMorphisms
  exact (e.mapHomologicalComplex (ComplexShape.up ℕ)).isEquivalence_functor

instance sheafPullback_isIso : IsIso (Int.sheafPullback f) := by
  change IsIso (((Int.imageComplexAdjunction f).homEquiv (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y)
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)).symm (Int.sheafDirectImage f))
  rw [Adjunction.homEquiv_counit]
  infer_instance

instance sheafPullbackInt_isIso : IsIso (Int.sheafPullbackInt f) := by
  exact ((AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso (Int.inverseImage f) ComplexShape.embeddingUpNat
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y)) ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X)).mapIso (asIso (Int.sheafPullback f))).isIso_hom

instance derivedInverseImage_isEquivalence : (Int.derivedInverseImage f).IsEquivalence := by
  let e := (Int.inverseImage f).asEquivalence
  let : e.functor.Additive := Int.inverseImageAdditive f
  exact DerivedEquivalenceIs.DerivedEquivalence.induced_isEquivalence e

instance derivedPullback_isIso : IsIso (Int.derivedPullback f) :=
  ((Int.inverseImage f).mapDerivedCategoryFactors.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R Y) ≪≫
    DerivedCategory.Q.mapIso (asIso (Int.sheafPullbackInt f))).isIso_hom

def isoPullback (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R Y n ≃ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X n :=
  (LinearEquiv.ofBijective ((Int.derivedInverseImage f).mapLinearMap R)
    ⟨(Int.derivedInverseImage f).map_injective, (Int.derivedInverseImage f).map_surjective⟩).trans
      (Linear.homCongr R (Int.derivedConstantIso f)
        (((Int.derivedInverseImage f).commShiftIso (n : ℤ)).app
            (DerivedCategory.Q.obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R Y)) ≪≫
          (shiftFunctor _ (n : ℤ)).mapIso (asIso (Int.derivedPullback f))))

theorem isoPullback_toLinearMap (n : ℕ) : (isoPullback f n).toLinearMap = Int.pullback f n := by
  apply LinearMap.ext
  intro α
  change ((Int.derivedConstantIso f).inv ≫ (Int.derivedInverseImage f).map α) ≫
      (((Int.derivedInverseImage f).commShiftIso (n : ℤ)).hom.app
          (DerivedCategory.Q.obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R Y)) ≫
        (shiftFunctor _ (n : ℤ)).map (Int.derivedPullback f)) = _
  simp only [Category.assoc]
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.IsoCohomology
