import OAI.AlgebraicGeometry.ComplexMultiplication.ConcreteRationalCoefficientCochains
import OAI.AlgebraicGeometry.ComplexMultiplication.SingularDualMap

/-! # Concrete Rational Naturality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.ConcreteRationalNaturality

noncomputable section

section

/-! # Actual scalar restriction and forgetting agree on cycles and cohomology -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- Forgetting module scalars retains the class of every actual closed representative. -/
theorem coefficientModuleHomologyπ {R : Type} [CommRing R]
    (K : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).homologyπ n ≫
        ((K.sc n).mapHomologyIso (forget₂ (ModuleCat R) AddCommGrpCat)).hom =
      ((K.sc n).mapCyclesIso (forget₂ (ModuleCat R) AddCommGrpCat)).hom ≫
        (forget₂ (ModuleCat R) AddCommGrpCat).map (K.homologyπ n) := by
  let F := forget₂ (ModuleCat R) AddCommGrpCat
  change ((K.sc n).map F).homologyπ ≫ ((K.sc n).mapHomologyIso F).hom =
    ((K.sc n).mapCyclesIso F).hom ≫ F.map ((K.sc n).homologyπ)
  let h := (K.sc n).homologyData.left
  rw [ShortComplex.LeftHomologyData.mapHomologyIso_eq h F,
    ShortComplex.LeftHomologyData.mapCyclesIso_eq h F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  rw [Category.assoc]
  change (h.map F).cyclesIso.hom ≫ F.map h.π ≫ F.map h.homologyIso.inv = _
  rw [← Functor.map_comp, ShortComplex.LeftHomologyData.π_comp_homologyIso_inv,
    Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Restricting scalars and then forgetting gives exactly the direct additive cycle comparison. -/
theorem coefficientRestriction_cycles_forgetting
    {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (K : CochainComplex (ModuleCat.{0} S) ℕ) (n : ℕ) :
    (((((ModuleCat.restrictScalars f).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).sc n).mapCyclesIso
          (forget₂ (ModuleCat R) AddCommGrpCat)).hom ≫
        (forget₂ (ModuleCat R) AddCommGrpCat).map
          (((K.sc n).mapCyclesIso (ModuleCat.restrictScalars f)).hom) =
      ((K.sc n).mapCyclesIso (forget₂ (ModuleCat S) AddCommGrpCat)).hom := by
  let F := ModuleCat.restrictScalars f
  let G := forget₂ (ModuleCat R) AddCommGrpCat
  let H := forget₂ (ModuleCat S) AddCommGrpCat
  change (((K.sc n).map F).mapCyclesIso G).hom ≫
    G.map (((K.sc n).mapCyclesIso F).hom) = ((K.sc n).mapCyclesIso H).hom
  apply (cancel_mono (H.map ((K.sc n).iCycles))).1
  rw [Category.assoc]
  change (((K.sc n).map F).mapCyclesIso G).hom ≫
      (G.map (((K.sc n).mapCyclesIso F).hom) ≫ G.map (F.map ((K.sc n).iCycles))) = _
  rw [← Functor.map_comp, ShortComplex.mapCyclesIso_hom_iCycles,
    ShortComplex.mapCyclesIso_hom_iCycles, ShortComplex.mapCyclesIso_hom_iCycles]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restricting scalars and then forgetting gives the direct additive cohomology comparison. -/
theorem coefficientRestriction_homology_forgetting
    {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (K : CochainComplex (ModuleCat.{0} S) ℕ) (n : ℕ) :
    (((((ModuleCat.restrictScalars f).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).sc n).mapHomologyIso
          (forget₂ (ModuleCat R) AddCommGrpCat)).hom ≫
        (forget₂ (ModuleCat R) AddCommGrpCat).map
          (((K.sc n).mapHomologyIso (ModuleCat.restrictScalars f)).hom) =
      ((K.sc n).mapHomologyIso (forget₂ (ModuleCat S) AddCommGrpCat)).hom := by
  let F := ModuleCat.restrictScalars f
  let G := forget₂ (ModuleCat R) AddCommGrpCat
  let H := forget₂ (ModuleCat S) AddCommGrpCat
  let KF := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  change (((K.sc n).map F).mapHomologyIso G).hom ≫
    G.map (((K.sc n).mapHomologyIso F).hom) = ((K.sc n).mapHomologyIso H).hom
  apply (cancel_epi (((K.sc n).map H).homologyπ)).1
  have hG : ((K.sc n).map H).homologyπ ≫
      (((K.sc n).map F).mapHomologyIso G).hom =
    (((K.sc n).map F).mapCyclesIso G).hom ≫ G.map (((K.sc n).map F).homologyπ) :=
    coefficientModuleHomologyπ KF n
  have hπ : ((K.sc n).map F).homologyπ ≫ ((K.sc n).mapHomologyIso F).hom =
      ((K.sc n).mapCyclesIso F).hom ≫ F.map ((K.sc n).homologyπ) := by
    let h := (K.sc n).homologyData.left
    rw [ShortComplex.LeftHomologyData.mapHomologyIso_eq h F,
      ShortComplex.LeftHomologyData.mapCyclesIso_eq h F]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
    rw [← Category.assoc, ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
    rw [Category.assoc]
    change (h.map F).cyclesIso.hom ≫ F.map h.π ≫ F.map h.homologyIso.inv = _
    rw [← Functor.map_comp, ShortComplex.LeftHomologyData.π_comp_homologyIso_inv,
      Functor.map_comp]
  have hH : ((K.sc n).map H).homologyπ ≫ ((K.sc n).mapHomologyIso H).hom =
      ((K.sc n).mapCyclesIso H).hom ≫ H.map ((K.sc n).homologyπ) :=
    coefficientModuleHomologyπ K n
  have hcy : (((K.sc n).map F).mapCyclesIso G).hom ≫
      G.map (((K.sc n).mapCyclesIso F).hom) = ((K.sc n).mapCyclesIso H).hom :=
    coefficientRestriction_cycles_forgetting f K n
  rw [← Category.assoc, hG, Category.assoc, ← Functor.map_comp,
    hπ, Functor.map_comp, ← Category.assoc, hcy, hH]
  rfl

end

/-! # Space naturality and additive normalization of the actual coefficient map -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- The actual rational coefficient inclusion commutes with every continuous pullback. -/
theorem actualRationalToComplexCochainMap_naturality {X Y : TopCat.{0}} (g : X ⟶ Y) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) g ≫ ConcreteRationalCoefficientCochains.actualRationalToComplexCochainMap X =
      ConcreteRationalCoefficientCochains.actualRationalToComplexCochainMap Y ≫
        ((ModuleCat.restrictScalars (algebraMap ℚ ℂ)).mapHomologicalComplex
          (ComplexShape.up ℕ)).map (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) g) := by
  let F := ModuleCat.restrictScalars (algebraMap ℚ ℂ)
  let FX := AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso (algebraMap ℚ ℂ) (ModuleCat.of ℂ ℂ) X
  let FY := AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso (algebraMap ℚ ℂ) (ModuleCat.of ℂ ℂ) Y
  have hi : AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (F.obj (ModuleCat.of ℂ ℂ)) g ≫ FX.inv =
      FY.inv ≫ (F.mapHomologicalComplex (ComplexShape.up ℕ)).map
        (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) g) := by
    apply (cancel_mono FX.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [show (F.mapHomologicalComplex (ComplexShape.up ℕ)).map
        (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) g) ≫ FX.hom =
          FY.hom ≫ AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (F.obj (ModuleCat.of ℂ ℂ)) g from
      AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso_naturality (algebraMap ℚ ℂ)
        (ModuleCat.of ℂ ℂ) g]
    simp
  dsimp only [ConcreteRationalCoefficientCochains.actualRationalToComplexCochainMap]
  rw [← Category.assoc, AlgebraicTopology.Cohomology.Singular.Functor.coefficientCochainMap_naturality, Category.assoc,
    ← Category.assoc (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℂ) g),
    AlgebraicTopology.Cohomology.Singular.Functor.coefficientCochainMap_naturality, Category.assoc, hi]
  simp only [Category.assoc]
  rfl

/-- Literal forgetting gives an additive map between the actual rational and complex cochains. -/
def actualAdditiveRationalToComplexCochainMap (Y : TopCat.{0}) :
    ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) Y) ⟶
      ((forget₂ (ModuleCat ℂ) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) Y) :=
  ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (ConcreteRationalCoefficientCochains.actualRationalToComplexCochainMap Y)

set_option backward.isDefEq.respectTransparency false in
/-- The additive coefficient map commutes with actual restriction to every subspace. -/
theorem actualAdditiveRationalToComplexCochainMap_naturality
    {X Y : TopCat.{0}} (g : X ⟶ Y) :
    ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) g) ≫
        actualAdditiveRationalToComplexCochainMap X =
      actualAdditiveRationalToComplexCochainMap Y ≫
        ((forget₂ (ModuleCat ℂ) AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.up ℕ)).map (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) g) := by
  simpa only [actualAdditiveRationalToComplexCochainMap, Functor.map_comp] using!
    congrArg (fun h => ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℕ)).map h) (actualRationalToComplexCochainMap_naturality g)

set_option backward.isDefEq.respectTransparency false in
/-- Additive cohomology normalization retains the existing ordinary coefficient inclusion. -/
theorem actualAdditiveRationalToComplexCochainMap_homology (Y : TopCat.{0}) (n : ℕ) :
    HomologicalComplex.homologyMap (actualAdditiveRationalToComplexCochainMap Y) n ≫
        (((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) Y).sc n).mapHomologyIso
          (forget₂ (ModuleCat ℂ) AddCommGrpCat)).hom =
      (((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) Y).sc n).mapHomologyIso
        (forget₂ (ModuleCat ℚ) AddCommGrpCat)).hom ≫
          (forget₂ (ModuleCat ℚ) AddCommGrpCat).map (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology Y n) := by
  let K := AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) Y
  let F := ModuleCat.restrictScalars (algebraMap ℚ ℂ)
  let G := forget₂ (ModuleCat ℚ) AddCommGrpCat
  let KF := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  have hb : HomologicalComplex.homologyMap (actualAdditiveRationalToComplexCochainMap Y) n ≫
      ((KF.sc n).mapHomologyIso G).hom =
    (((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) Y).sc n).mapHomologyIso G).hom ≫
      G.map (HomologicalComplex.homologyMap (ConcreteRationalCoefficientCochains.actualRationalToComplexCochainMap Y) n) :=
    SingularDualMap.forgottenModuleComplex_homology_naturality ℚ (ConcreteRationalCoefficientCochains.actualRationalToComplexCochainMap Y) n
  have hcf : ((KF.sc n).mapHomologyIso G).hom ≫
      G.map (((K.sc n).mapHomologyIso F).hom) =
    ((K.sc n).mapHomologyIso (forget₂ (ModuleCat ℂ) AddCommGrpCat)).hom :=
    coefficientRestriction_homology_forgetting (algebraMap ℚ ℂ) K n
  rw [← hcf, ← Category.assoc, hb,
    Category.assoc, ← Functor.map_comp, ConcreteRationalCoefficientCochains.actualRationalToComplexCochainMap_homology]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.ConcreteRationalNaturality
