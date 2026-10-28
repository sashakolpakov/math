import OAI.AlgebraicGeometry.Comparison.Betti.Derived.ShiftCoherence

/-! # Functor Iso -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Derived.FunctorIso

noncomputable section

/-! A constructed isomorphism of exact functors induces a normalized derived isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.CategoryTheory.Limits

universe w w' u u' v v'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)

def functorIsoBeforeLocalization : DerivedCategory.Q ⋙ F.mapDerivedCategory ≅
    DerivedCategory.Q ⋙ G.mapDerivedCategory :=
  F.mapDerivedCategoryFactors ≪≫
    isoWhiskerRight (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)) DerivedCategory.Q ≪≫
    G.mapDerivedCategoryFactors.symm

instance functorIsoBeforeLocalizationCommShift :
    NatTrans.CommShift (functorIsoBeforeLocalization e).hom ℤ := by
  change NatTrans.CommShift
    (F.mapDerivedCategoryFactors.hom ≫
      Functor.whiskerRight (NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)) DerivedCategory.Q ≫
      G.mapDerivedCategoryFactors.inv) ℤ
  infer_instance

def functorIso : F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  (Localization.fullyFaithfulWhiskeringLeft
    (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C)
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (DerivedCategory D)).preimageIso
      (functorIsoBeforeLocalization e)

theorem functorIso_normalization :
    Functor.whiskerLeft DerivedCategory.Q (functorIso e).hom =
      (functorIsoBeforeLocalization e).hom :=
  (Localization.fullyFaithfulWhiskeringLeft
    (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C)
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (DerivedCategory D)).map_preimage
      (functorIsoBeforeLocalization e).hom

theorem functorIso_hom_app (K : CochainComplex C ℤ) :
    (functorIso e).hom.app (DerivedCategory.Q.obj K) =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app K) ≫
          G.mapDerivedCategoryFactors.inv.app K :=
  congr_app (functorIso_normalization e) K

instance functorIsoCommShift : NatTrans.CommShift (functorIso e).hom ℤ := by
  have : NatTrans.CommShift (Functor.whiskerLeft DerivedCategory.Q (functorIso e).hom) ℤ := by
    rw [functorIso_normalization]
    infer_instance
  exact ShiftCoherence.commShift_of_localization
    (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C)
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (functorIso e).hom

end

end OAI.AlgebraicGeometry.Comparison.Betti.Derived.FunctorIso
