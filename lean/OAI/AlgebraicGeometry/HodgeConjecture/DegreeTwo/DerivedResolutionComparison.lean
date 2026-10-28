import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueDerivedNaturality

/-! # Derived Resolution Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DerivedResolutionComparison.Constructions

noncomputable section

/-! A comparison of the resolved sheaves intertwines actual maps on section cohomology in all degrees. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}}
variable (K L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
variable (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (heK : ∀ n, K.ExactAt (n+1))
variable (hL : ∀ n, TopCat.Sheaf.IsFlasque (L.X n)) (heL : ∀ n, L.ExactAt (n+1))

def derivedResolutionSectionIso (e : K.homology 0 ≅ L.homology 0) (U : Opens X) (n : ℕ) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U K).homology n ≅ (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U L).homology n :=
  FlasqueDerivedComparison.Constructions.flasqueResolutionDerivedCohomologyIso K hK heK U n ≪≫
    ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).rightDerived n).mapIso e ≪≫
    (FlasqueDerivedComparison.Constructions.flasqueResolutionDerivedCohomologyIso L hL heL U n).symm

theorem derivedResolutionSectionIso_comm
    (A : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
    (hA : ∀ n, TopCat.Sheaf.IsFlasque (A.X n)) (heA : ∀ n, A.ExactAt (n+1))
    (f : A ⟶ K) (g : A ⟶ L) (e : K.homology 0 ≅ L.homology 0)
    (he : HomologicalComplex.homologyMap f 0 ≫ e.hom = HomologicalComplex.homologyMap g 0)
    (U : Opens X) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).mapHomologicalComplex (ComplexShape.up ℕ)).map f) n ≫
        (derivedResolutionSectionIso K L hK heK hL heL e U n).hom =
      HomologicalComplex.homologyMap
        (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).mapHomologicalComplex (ComplexShape.up ℕ)).map g) n := by
  apply (cancel_mono (FlasqueDerivedComparison.Constructions.flasqueResolutionDerivedCohomologyIso L hL heL U n).hom).mp
  simp only [derivedResolutionSectionIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, FlasqueDerivedNaturality.Constructions.flasqueResolutionDerivedCohomologyIso_naturality f hA heA hK heK,
    Category.assoc, ← Functor.map_comp, he,
    FlasqueDerivedNaturality.Constructions.flasqueResolutionDerivedCohomologyIso_naturality g hA heA hL heL]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DerivedResolutionComparison.Constructions
