import OAI.NumberTheory.PadicHodge.GeometricComparison.AugmentedInjective
import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ComplexTransportNaturality

/-! # Augmented Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.AugmentedNaturality.AugmentedComparisonNaturality

noncomputable section

/-! Augmented injective comparisons are natural up to homotopy under an
exact coefficient or site restriction functor. -/

open _root_.CategoryTheory

universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
  {Z : C} {Z' : D} (e : F.obj Z ≅ Z')
  (K : CochainComplex C ℕ) (a : (CochainComplex.single₀ C).obj Z ⟶ K) (ha : QuasiIso a)
  (L : CochainComplex D ℕ) (b : (CochainComplex.single₀ D).obj Z' ⟶ L) (hb : QuasiIso b)
  (I : InjectiveResolution Z) (I' : InjectiveResolution Z')
  (s : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶ L)
  (t : (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ I'.cocomplex)
  (hs : IntegralComparison.Single.ComplexTransport.map F e a ≫ s = b)
  (ht : IntegralComparison.Single.ComplexTransport.map F e I.ι ≫ t = I'.ι)

def first := (F.mapHomologicalComplex (.up ℕ)).map (AugmentedInjective.AugmentedInjectiveComparison.map K a ha I) ≫ t
def second := s ≫ AugmentedInjective.AugmentedInjectiveComparison.map L b hb I'

include ht in
omit [F.PreservesHomology] in
theorem first_augmentation : IntegralComparison.Single.ComplexTransport.map F e a ≫ first F K a ha I I' t = I'.ι :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun x => x ≫ t)
      ((IntegralComparison.Single.ComplexTransportNaturality.comp F e a (AugmentedInjective.AugmentedInjectiveComparison.map K a ha I)).trans
        (congrArg (IntegralComparison.Single.ComplexTransport.map F e) (AugmentedInjective.AugmentedInjectiveComparison.augmentation K a ha I)))).trans ht)

include hs in
omit [F.PreservesHomology] in
theorem second_augmentation : IntegralComparison.Single.ComplexTransport.map F e a ≫ second F K L b hb I' s = I'.ι :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun x => x ≫ AugmentedInjective.AugmentedInjectiveComparison.map L b hb I') hs).trans
      (AugmentedInjective.AugmentedInjectiveComparison.augmentation L b hb I'))

def homotopy : Homotopy (first F K a ha I I' t) (second F K L b hb I' s) := by
  let := ha
  let : QuasiIso (IntegralComparison.Single.ComplexTransport.map F e a) :=
    IntegralComparison.Single.ComplexTransportNaturality.quasiIso F e a
  exact IntegralComparison.Augmented.ResolutionHomotopy.homotopy _ (IntegralComparison.Single.ComplexTransport.map F e a) I' _ _
    ((first_augmentation F e K a ha I I' t ht).trans
      (second_augmentation F e K a L b hb I' s hs).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.AugmentedNaturality.AugmentedComparisonNaturality
