import OAI.AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalVanishing
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Rational Relative Homology -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles

noncomputable section

/-!
# Rational coefficients on actual relative singular homology

Rationalizing the actual integral relative singular-chain quotient gives the
actual rational relative singular-chain quotient. The comparison is induced
by the natural coefficient comparison on absolute singular chains and by
preservation of cokernels. Exactness of rationalization then identifies its
homology with the rationalization of integral relative homology.

The known integral calculation of the complex normal local groups therefore
gives the rational calculation, in all degrees including complex dimension
zero.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Degreewise extension of integral chain complexes to rational coefficients. -/
abbrev rationalizeChains :
    ChainComplex (ModuleCat.{0} ℤ) ℕ ⥤ ChainComplex (ModuleCat.{0} ℚ) ℕ :=
  RationalScalarExtension.Cycles.rationalizeModules.mapHomologicalComplex (ComplexShape.down ℕ)

/-- Rationalization commutes with the actual relative singular-chain quotient. -/
def rationalRelativeChainsIso (X : TopCat.{0}) (A : Set X) :
    rationalizeChains.obj (LocalHomology.Cycles.relativeSingularChains X A) ≅ RelativeScalarChains.Cycles.relativeScalarChains ℚ X A :=
  PreservesCokernel.iso rationalizeChains (LocalHomology.Cycles.subspaceChainInclusion X A) ≪≫
    cokernel.mapIso
      (rationalizeChains.map (LocalHomology.Cycles.subspaceChainInclusion X A))
      (RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ X A)
      (RationalSingularChains.Cycles.rationalSingularChainsIso (TopCat.of A)) (RationalSingularChains.Cycles.rationalSingularChainsIso X)
      (RationalSingularChains.Cycles.rationalSingularChainsIso_hom_naturality (LocalHomology.Cycles.subspaceInclusion X A))

/-- The comparison commutes with the actual absolute-to-relative quotient maps. -/
@[reassoc]
theorem rationalRelativeChainsIso_projection (X : TopCat.{0}) (A : Set X) :
    rationalizeChains.map (LocalHomology.Cycles.relativeChainProjection X A) ≫
        (rationalRelativeChainsIso X A).hom =
      (RationalSingularChains.Cycles.rationalSingularChainsIso X).hom ≫ RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A := by
  dsimp only [rationalRelativeChainsIso, Iso.trans_hom, cokernel.mapIso_hom]
  rw [← Category.assoc, PreservesCokernel.π_iso_hom, cokernel.π_desc]

/-- The relative rationalization comparison is natural for actual maps of pairs. -/
@[reassoc]
theorem rationalRelativeChainsIso_hom_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) :
    rationalizeChains.map (LocalHomology.Cycles.relativeSingularChainsMap f h) ≫
        (rationalRelativeChainsIso Y B).hom =
      (rationalRelativeChainsIso X A).hom ≫ RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f h := by
  apply (cancel_epi (rationalizeChains.map (LocalHomology.Cycles.relativeChainProjection X A))).mp
  calc
    _ = rationalizeChains.map
        (LocalHomology.Cycles.relativeChainProjection X A ≫ LocalHomology.Cycles.relativeSingularChainsMap f h) ≫
          (rationalRelativeChainsIso Y B).hom := by
      rw [rationalizeChains.map_comp, Category.assoc]
    _ = rationalizeChains.map (LocalHomology.Cycles.integralSingularChainFunctor.map f) ≫
        rationalizeChains.map (LocalHomology.Cycles.relativeChainProjection Y B) ≫
          (rationalRelativeChainsIso Y B).hom := by
      rw [LocalHomology.Cycles.relativeChainProjection_naturality, rationalizeChains.map_comp, Category.assoc]
    _ = rationalizeChains.map (LocalHomology.Cycles.integralSingularChainFunctor.map f) ≫
        (RationalSingularChains.Cycles.rationalSingularChainsIso Y).hom ≫ RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ Y B := by
      rw [rationalRelativeChainsIso_projection]
    _ = (RationalSingularChains.Cycles.rationalSingularChainsIso X).hom ≫
        (RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map f ≫ RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ Y B := by
      rw [← Category.assoc, RationalSingularChains.Cycles.rationalSingularChainsIso_hom_naturality, Category.assoc]
    _ = (RationalSingularChains.Cycles.rationalSingularChainsIso X).hom ≫ RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A ≫
        RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f h := by
      rw [RelativeScalarChains.Cycles.relativeScalarChainProjection_naturality]
    _ = _ := by
      rw [← Category.assoc, ← rationalRelativeChainsIso_projection, Category.assoc]

/-- The inverse comparison is also natural for actual maps of pairs. -/
@[reassoc]
theorem rationalRelativeChainsIso_inv_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) :
    RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f h ≫ (rationalRelativeChainsIso Y B).inv =
      (rationalRelativeChainsIso X A).inv ≫
        rationalizeChains.map (LocalHomology.Cycles.relativeSingularChainsMap f h) := by
  calc
    _ = (rationalRelativeChainsIso X A).inv ≫
        ((rationalRelativeChainsIso X A).hom ≫ RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f h) ≫
          (rationalRelativeChainsIso Y B).inv := by simp
    _ = (rationalRelativeChainsIso X A).inv ≫
        (rationalizeChains.map (LocalHomology.Cycles.relativeSingularChainsMap f h) ≫
          (rationalRelativeChainsIso Y B).hom) ≫
          (rationalRelativeChainsIso Y B).inv := by
      rw [← rationalRelativeChainsIso_hom_naturality]
    _ = _ := by simp

/-- Rational relative homology is the scalar extension of the actual integral relative group. -/
def rationalRelativeHomologyIso (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A n ≅
      RationalScalarExtension.Cycles.rationalizeModules.obj (LocalHomology.Cycles.relativeSingularHomology X A n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n).mapIso
      (rationalRelativeChainsIso X A).symm ≪≫
    RationalScalarExtension.Cycles.rationalizeHomologyIso (LocalHomology.Cycles.relativeSingularChains X A) n

/-- The homology-level scalar-extension identification respects every actual map of pairs. -/
@[reassoc]
theorem rationalRelativeHomologyIso_hom_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) (n : ℕ) :
    HomologicalComplex.homologyMap (RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f h) n ≫
        (rationalRelativeHomologyIso Y B n).hom =
      (rationalRelativeHomologyIso X A n).hom ≫
        RationalScalarExtension.Cycles.rationalizeModules.map (LocalHomology.Cycles.relativeSingularHomologyMap f h n) := by
  have hnat := congrArg (fun g => HomologicalComplex.homologyMap g n)
    (rationalRelativeChainsIso_inv_naturality f h)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hnat
  change HomologicalComplex.homologyMap (RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f h) n ≫
      (HomologicalComplex.homologyMap (rationalRelativeChainsIso Y B).inv n ≫
        (RationalScalarExtension.Cycles.rationalizeHomologyIso (LocalHomology.Cycles.relativeSingularChains Y B) n).hom) =
    (HomologicalComplex.homologyMap (rationalRelativeChainsIso X A).inv n ≫
        (RationalScalarExtension.Cycles.rationalizeHomologyIso (LocalHomology.Cycles.relativeSingularChains X A) n).hom) ≫
      RationalScalarExtension.Cycles.rationalizeModules.map (LocalHomology.Cycles.relativeSingularHomologyMap f h n)
  rw [← Category.assoc, hnat, Category.assoc, RationalScalarExtension.Cycles.rationalizeHomologyIso_hom_naturality,
    ← Category.assoc]

/-- Vanishing of integral relative homology implies vanishing with rational coefficients. -/
theorem rationalRelativeHomology_isZero (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (h : IsZero (LocalHomology.Cycles.relativeSingularHomology X A n)) :
    IsZero (RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A n) :=
  (RationalScalarExtension.Cycles.rationalizeModules.map_isZero h).of_iso (rationalRelativeHomologyIso X A n)

/-- The actual top rational local homology of a complex coordinate normal space is `ℚ`. -/
def complexNormalRationalTopLocalHomologyIso (p : ℕ) :
    RelativeScalarChains.Cycles.localScalarHomology ℚ (TopCat.of (Fin p → ℂ)) 0 (2 * p) ≅ ModuleCat.of ℚ ℚ :=
  rationalRelativeHomologyIso (TopCat.of (Fin p → ℂ)) ({0}ᶜ : Set (Fin p → ℂ)) (2 * p) ≪≫
    RationalScalarExtension.Cycles.rationalizeModules.mapIso (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p) ≪≫ RationalScalarExtension.Cycles.rationalizeUnitIso

/-- Every rational local homology group outside real degree `2*p` vanishes. -/
theorem complexNormalRationalLocalHomology_isZero (p n : ℕ) (hn : n ≠ 2 * p) :
    IsZero (RelativeScalarChains.Cycles.localScalarHomology ℚ (TopCat.of (Fin p → ℂ)) 0 n) :=
  rationalRelativeHomology_isZero (TopCat.of (Fin p → ℂ)) ({0}ᶜ : Set (Fin p → ℂ)) n
    (ComplexLocalVanishing.Cycles.complexNormalLocalHomology_isZero p n hn)

/-- The top rational local group is nonzero. -/
theorem complexNormalRationalTopLocalHomology_not_isZero (p : ℕ) :
    ¬ IsZero (RelativeScalarChains.Cycles.localScalarHomology ℚ (TopCat.of (Fin p → ℂ)) 0 (2 * p)) := by
  intro h
  have hQ := h.of_iso (complexNormalRationalTopLocalHomologyIso p).symm
  let : Subsingleton ℚ := ModuleCat.isZero_iff_subsingleton.mp hQ
  exact zero_ne_one (Subsingleton.elim (0 : ℚ) 1)

/-- Rational normal local homology is concentrated exactly in its real top degree. -/
theorem complexNormalRationalLocalHomology_isZero_iff (p n : ℕ) :
    IsZero (RelativeScalarChains.Cycles.localScalarHomology ℚ (TopCat.of (Fin p → ℂ)) 0 n) ↔ n ≠ 2 * p := by
  constructor
  · intro h hn
    subst n
    exact complexNormalRationalTopLocalHomology_not_isZero p h
  · exact complexNormalRationalLocalHomology_isZero p n

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles
