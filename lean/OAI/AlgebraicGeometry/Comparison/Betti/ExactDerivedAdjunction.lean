import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Adjunction
import OAI.AlgebraicGeometry.Comparison.Betti.Derived.ResolutionNaturality
import Mathlib.CategoryTheory.Localization.Adjunction

/-! # Exact Derived Adjunction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ExactDerivedAdjunction

noncomputable section

/-! Actual exact adjunctions descend to the chosen derived-category functors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe w₁ w₂ u₁ u₂ v₁ v₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]

instance exactFunctorCatCommSq (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    CatCommSq (F.mapHomologicalComplex (ComplexShape.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q F.mapDerivedCategory := ⟨F.mapDerivedCategoryFactors.symm⟩

variable {F : C ⥤ D} {G : D ⥤ C}
  [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

def exactAdjunction (adj : F ⊣ G) : F.mapDerivedCategory ⊣ G.mapDerivedCategory :=
  (Complex.Adjunction.onComplexes adj (ComplexShape.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
    F.mapDerivedCategory G.mapDerivedCategory

theorem exactAdjunction_unit (adj : F ⊣ G) (K : CochainComplex C ℤ) :
    (exactAdjunction adj).unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((Complex.Adjunction.onComplexes adj (ComplexShape.up ℤ)).unit.app K) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
          G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) :=
  Adjunction.localization_unit_app _ _ _ _ _ _ _ K

theorem exactAdjunction_counit (adj : F ⊣ G) (L : CochainComplex D ℤ) :
    (exactAdjunction adj).counit.app (DerivedCategory.Q.obj L) =
      F.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app L) ≫
        F.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≫
          DerivedCategory.Q.map ((Complex.Adjunction.onComplexes adj (ComplexShape.up ℤ)).counit.app L) :=
  Adjunction.localization_counit_app _ _ _ _ _ _ _ L

theorem exactAdjunction_homEquiv (adj : F ⊣ G)
    {K : CochainComplex C ℤ} {L : CochainComplex D ℤ}
    (f : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ L) :
    (exactAdjunction adj).homEquiv (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
        (Derived.ResolutionNaturality.Ext.derivedComplexMap F f) =
      DerivedCategory.Q.map ((Complex.Adjunction.onComplexes adj (ComplexShape.up ℤ)).homEquiv K L f) ≫
        G.mapDerivedCategoryFactors.inv.app L := by
  let QC : CochainComplex C ℤ ⥤ DerivedCategory C := DerivedCategory.Q
  let QD : CochainComplex D ℤ ⥤ DerivedCategory D := DerivedCategory.Q
  let a := F.mapDerivedCategoryFactors.app K
  let b := G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  let c := G.mapDerivedCategoryFactors.app L
  let u := (Complex.Adjunction.onComplexes adj (ComplexShape.up ℤ)).unit.app K
  let t := (G.mapHomologicalComplex (ComplexShape.up ℤ)).map f
  have hn : b.inv ≫ G.mapDerivedCategory.map (QD.map f) = QC.map t ≫ c.inv :=
    (G.mapDerivedCategoryFactors.inv.naturality f).symm
  rw [Adjunction.homEquiv_unit, exactAdjunction_unit]
  change (QC.map u ≫ b.inv ≫ G.mapDerivedCategory.map a.inv) ≫
    G.mapDerivedCategory.map (a.hom ≫ QD.map f) =
      QC.map ((Complex.Adjunction.onComplexes adj (ComplexShape.up ℤ)).homEquiv K L f) ≫ c.inv
  erw [G.mapDerivedCategory.map_comp a.hom (QD.map f)]
  simp only [Category.assoc, Iso.map_inv_hom_id_assoc]
  rw [hn, ← Category.assoc, ← QC.map_comp]
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.ExactDerivedAdjunction
