import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.ZariskiComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechFunctor

/-! # Cohomology Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.CohomologyNaturality

noncomputable section

/-! Projection to ordered Cech cochains and the positive-degree comparison with genuine cohomology are natural in the actual module sheaf. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u

variable {X : Scheme.{u}} {R : Type u} [CommRing R]
variable (c : R →+* Γ(X, ⊤)) {M N : X.Modules} (a : M ⟶ N)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

theorem coefficientCechToOrdered_naturality :
    ((Intrinsic.CoefficientCechComplex.coefficientCechComplexFunctor c U).map a) ≫ ComplexProjection.coefficientCechToOrdered c N U =
      ComplexProjection.coefficientCechToOrdered c M U ≫ ((Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).map a) := by
  apply HomologicalComplex.Hom.ext
  funext n
  let E : (X.Opensᵒᵖ ⥤ ModuleCat.{u} R) ⥤
      ((FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤ ModuleCat.{u} R) :=
    FormalCoproduct.evalOp.{u} X.Opens (ModuleCat.{u} R)
  let α := E.map ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).map a)
  exact (α.naturality (FormalProjection.orderedCechFormalInclusion U n).op).symm

theorem coefficientCechOrderedHomologyIso_naturality (n : ℕ) :
    HomologicalComplex.homologyMap ((Intrinsic.CoefficientCechComplex.coefficientCechComplexFunctor c U).map a) n ≫
        (Ordered.CoefficientCechHomotopyEquivalence.coefficientCechOrderedHomologyIso c N U n).hom =
      (Ordered.CoefficientCechHomotopyEquivalence.coefficientCechOrderedHomologyIso c M U n).hom ≫
        HomologicalComplex.homologyMap ((Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).map a) n := by
  let α : Intrinsic.CoefficientCechComplex.coefficientCechComplex c M U ⟶ Intrinsic.CoefficientCechComplex.coefficientCechComplex c N U :=
    (Intrinsic.CoefficientCechComplex.coefficientCechComplexFunctor c U).map a
  let β : Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c N U :=
    (Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).map a
  have h : α ≫ ComplexProjection.coefficientCechToOrdered c N U = ComplexProjection.coefficientCechToOrdered c M U ≫ β :=
    coefficientCechToOrdered_naturality c a U
  change HomologicalComplex.homologyMap α n ≫
      HomologicalComplex.homologyMap (ComplexProjection.coefficientCechToOrdered c N U) n =
    HomologicalComplex.homologyMap (ComplexProjection.coefficientCechToOrdered c M U) n ≫
      HomologicalComplex.homologyMap β n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    h]

theorem coefficientCechOrderedHomologyIso_inv_naturality (n : ℕ) :
    HomologicalComplex.homologyMap ((Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).map a) n ≫
        (Ordered.CoefficientCechHomotopyEquivalence.coefficientCechOrderedHomologyIso c N U n).inv =
      (Ordered.CoefficientCechHomotopyEquivalence.coefficientCechOrderedHomologyIso c M U n).inv ≫
        HomologicalComplex.homologyMap ((Intrinsic.CoefficientCechComplex.coefficientCechComplexFunctor c U).map a) n := by
  let α : Intrinsic.CoefficientCechComplex.coefficientCechComplex c M U ⟶ Intrinsic.CoefficientCechComplex.coefficientCechComplex c N U :=
    (Intrinsic.CoefficientCechComplex.coefficientCechComplexFunctor c U).map a
  let β : Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c N U :=
    (Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).map a
  have h : HomologicalComplex.homologyMap α n ≫ (Ordered.CoefficientCechHomotopyEquivalence.coefficientCechOrderedHomologyIso c N U n).hom =
      (Ordered.CoefficientCechHomotopyEquivalence.coefficientCechOrderedHomologyIso c M U n).hom ≫ HomologicalComplex.homologyMap β n :=
    coefficientCechOrderedHomologyIso_naturality c a U n
  change HomologicalComplex.homologyMap β n ≫ (Ordered.CoefficientCechHomotopyEquivalence.coefficientCechOrderedHomologyIso c N U n).inv =
    (Ordered.CoefficientCechHomotopyEquivalence.coefficientCechOrderedHomologyIso c M U n).inv ≫ HomologicalComplex.homologyMap α n
  apply (cancel_epi (Ordered.CoefficientCechHomotopyEquivalence.coefficientCechOrderedHomologyIso c M U n).hom).mp
  rw [← Category.assoc, ← h,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

variable [X.IsSeparated] [M.IsQuasicoherent] [N.IsQuasicoherent]
variable (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))

omit [LinearOrder ι] in
theorem coefficientCechZariskiModuleIso_naturality (n : ℕ) :
    HomologicalComplex.homologyMap
        (K := Intrinsic.CoefficientCechComplex.coefficientCechComplex c M U) (L := Intrinsic.CoefficientCechComplex.coefficientCechComplex c N U)
        ((Intrinsic.CoefficientCechComplex.coefficientCechComplexFunctor c U).map a) (n + 1) ≫
        (CoefficientCech.ZariskiLinearity.coefficientCechZariskiModuleIso c N U hU ha n).hom =
      (CoefficientCech.ZariskiLinearity.coefficientCechZariskiModuleIso c M U hU ha n).hom ≫
        (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (n + 1)).map a := by
  apply (forget₂ (ModuleCat R) AddCommGrpCat).map_injective
  exact CoefficientCech.ZariskiComparison.coefficientCechZariskiAddIso_naturality c a U hU ha n

theorem orderedCechZariskiModuleIso_naturality (n : ℕ) :
    HomologicalComplex.homologyMap ((Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).map a) (n + 1) ≫
        (ZariskiComparison.orderedCechZariskiModuleIso c N U hU ha n).hom =
      (ZariskiComparison.orderedCechZariskiModuleIso c M U hU ha n).hom ≫
        (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (n + 1)).map a := by
  let α : Intrinsic.CoefficientCechComplex.coefficientCechComplex c M U ⟶ Intrinsic.CoefficientCechComplex.coefficientCechComplex c N U :=
    (Intrinsic.CoefficientCechComplex.coefficientCechComplexFunctor c U).map a
  let β : Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c N U :=
    (Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).map a
  have h₁ : HomologicalComplex.homologyMap β (n + 1) ≫
        (Ordered.CoefficientCechHomotopyEquivalence.coefficientCechOrderedHomologyIso c N U (n + 1)).inv =
      (Ordered.CoefficientCechHomotopyEquivalence.coefficientCechOrderedHomologyIso c M U (n + 1)).inv ≫ HomologicalComplex.homologyMap α (n + 1) :=
    coefficientCechOrderedHomologyIso_inv_naturality c a U (n + 1)
  have h₂ : HomologicalComplex.homologyMap α (n + 1) ≫ (CoefficientCech.ZariskiLinearity.coefficientCechZariskiModuleIso c N U hU ha n).hom =
      (CoefficientCech.ZariskiLinearity.coefficientCechZariskiModuleIso c M U hU ha n).hom ≫
        (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (n + 1)).map a :=
    coefficientCechZariskiModuleIso_naturality c a U hU ha n
  change HomologicalComplex.homologyMap β (n + 1) ≫
      ((Ordered.CoefficientCechHomotopyEquivalence.coefficientCechOrderedHomologyIso c N U (n + 1)).inv ≫
        (CoefficientCech.ZariskiLinearity.coefficientCechZariskiModuleIso c N U hU ha n).hom) =
    ((Ordered.CoefficientCechHomotopyEquivalence.coefficientCechOrderedHomologyIso c M U (n + 1)).inv ≫
      (CoefficientCech.ZariskiLinearity.coefficientCechZariskiModuleIso c M U hU ha n).hom) ≫ _
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.CohomologyNaturality
