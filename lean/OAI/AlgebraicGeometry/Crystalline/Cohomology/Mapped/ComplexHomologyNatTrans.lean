import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology

/-! # Complex Homology Nat Trans -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomologyNatTrans.MappedComplexHomologyNatTrans

noncomputable section

/-! # Canonical homology transport is natural in the coefficient functor -/

open _root_.CategoryTheory

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {F G : C ⥤ D} [F.Additive] [F.PreservesHomology]
  [G.Additive] [G.PreservesHomology] (τ : F ⟶ G)
  (K : CochainComplex C ℕ)

theorem naturality (n : ℕ) :
    HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex τ (.up ℕ)).app K) n ≫
        (ComplexHomology.MappedComplexHomology.iso G K n).hom =
      (ComplexHomology.MappedComplexHomology.iso F K n).hom ≫ τ.app (K.homology n) := by
  change ShortComplex.homologyMap ((K.sc n).mapNatTrans τ) ≫
    ((K.sc n).mapHomologyIso G).hom = ((K.sc n).mapHomologyIso F).hom ≫ τ.app (K.sc n).homology
  rw [ShortComplex.homologyMap_mapNatTrans, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomologyNatTrans.MappedComplexHomologyNatTrans
