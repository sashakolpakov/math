import OAI.AlgebraicTopology.Cohomology.Singular.Basic
import OAI.AlgebraicTopology.Cohomology.Singular.Functor
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Chains -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.Chains

noncomputable section

/-!
# Restricting scalars in genuine singular cohomology

Restriction of scalars commutes with the products defining singular cochains
and is exact. The resulting comparison identifies cohomology computed with
complex-valued rational cochains with ordinary complex-module cohomology,
viewed as a rational module. No finite dimensionality assumption is required.
-/

open _root_.CategoryTheory Opposite _root_.CategoryTheory.Limits
open scoped Simplicial

section CoproductComparison

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]
variable [HasCoproducts.{0} C] [HasCoproducts.{0} D]
variable [Preadditive C] [Preadditive D]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison from simplicial chains on the image coefficient
to the image of the simplicial chain complex. -/
def simplicialChainsComparison (F : C ⥤ D) [F.Additive]
    (K : SSet.{0}) (M : C) :
    K.chainComplex (F.obj M) ⟶
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (K.chainComplex M) where
  f n := sigmaComparison F (fun _ : K _⦋n⦌ => M)
  comm' := by
    rintro i n (rfl : n + 1 = i)
    apply K.chainComplex_hom_ext
    intro x
    change K.ιChainComplex x ≫
      sigmaComparison F (fun _ : K _⦋n + 1⦌ => M) ≫
        F.map ((K.chainComplex M).d (n + 1) n) =
      K.ιChainComplex x ≫ (K.chainComplex (F.obj M)).d (n + 1) n ≫
        sigmaComparison F (fun _ : K _⦋n⦌ => M)
    rw [← Category.assoc]
    erw [ι_comp_sigmaComparison, ← F.map_comp, K.ιChainComplex_d]
    rw [F.map_sum]
    simp only [F.map_zsmul]
    rw [← Category.assoc]
    erw [K.ιChainComplex_d, Preadditive.sum_comp]
    simp only [Preadditive.zsmul_comp, SSet.ιChainComplex,
      ι_comp_sigmaComparison]

/-- Preservation of small coproducts turns the comparison into an isomorphism
of actual chain complexes, including their differentials. -/
def simplicialChainsComparisonIso (F : C ⥤ D) [F.Additive]
    [PreservesColimitsOfSize.{0,0} F] (K : SSet.{0}) (M : C) :
    K.chainComplex (F.obj M) ≅
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (K.chainComplex M) := by
  haveI (n : ℕ) : IsIso ((simplicialChainsComparison F K M).f n) := by
    change IsIso (sigmaComparison F (fun _ : K _⦋n⦌ => M))
    infer_instance
  haveI := HomologicalComplex.Hom.isIso_of_components
    (simplicialChainsComparison F K M)
  exact asIso (simplicialChainsComparison F K M)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison commutes with maps of the underlying simplicial sets. -/
theorem simplicialChainsComparison_naturality (F : C ⥤ D) [F.Additive]
    {K L : SSet.{0}} (g : K ⟶ L) (M : C) :
    SSet.chainComplexMap g (F.obj M) ≫ simplicialChainsComparison F L M =
      simplicialChainsComparison F K M ≫
        (F.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (SSet.chainComplexMap g M) := by
  ext n : 1
  apply K.chainComplex_hom_ext
  intro x
  change K.ιChainComplex x ≫ (SSet.chainComplexMap g (F.obj M)).f n ≫
      sigmaComparison F (fun _ : L _⦋n⦌ => M) =
    K.ιChainComplex x ≫ sigmaComparison F (fun _ : K _⦋n⦌ => M) ≫
      F.map ((SSet.chainComplexMap g M).f n)
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  erw [ι_comp_sigmaComparison]
  rw [← Category.assoc]
  erw [ι_comp_sigmaComparison, ← F.map_comp, SSet.ι_chainComplexMap_f]
  rfl

end CoproductComparison

variable {R S : Type} [CommRing R] [CommRing S]

/-- Restricting coefficients commutes with genuine simplicial cochains. -/
def simplicialCochainsRestrictScalarsIso (f : R →+* S)
    (K : SSet.{0}) (M : ModuleCat.{0} S) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (Basic.simplicialCochains K M) ≅
      Basic.simplicialCochains K ((ModuleCat.restrictScalars f).obj M) := by
  let F := ModuleCat.restrictScalars.{0} f
  haveI : PreservesColimitsOfSize.{0,0} F.op :=
    preservesColimitsOfSize_op F
  exact (HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).mapIso
    (simplicialChainsComparisonIso F.op K (op M)).op

/-- The scalar-restriction isomorphism for singular cochain complexes. -/
def singularCochainsRestrictScalarsIso (f : R →+* S)
    (M : ModuleCat.{0} S) (X : TopCat.{0}) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (Basic.singularCochains M X) ≅
      Basic.singularCochains ((ModuleCat.restrictScalars f).obj M) X :=
  simplicialCochainsRestrictScalarsIso f (TopCat.toSSet.obj X) M

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Scalar restriction commutes with pullback of singular cochains. -/
theorem singularCochainsRestrictScalarsIso_naturality (f : R →+* S)
    (M : ModuleCat.{0} S) {X Y : TopCat.{0}} (g : X ⟶ Y) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (Functor.singularPullback M g) ≫ (singularCochainsRestrictScalarsIso f M X).hom =
      (singularCochainsRestrictScalarsIso f M Y).hom ≫
        Functor.singularPullback ((ModuleCat.restrictScalars f).obj M) g := by
  let F := ModuleCat.restrictScalars.{0} f
  have h := simplicialChainsComparison_naturality F.op (TopCat.toSSet.map g) (op M)
  ext n : 1
  apply Quiver.Hom.op_inj
  simpa [singularCochainsRestrictScalarsIso, simplicialCochainsRestrictScalarsIso,
    simplicialChainsComparisonIso, Functor.singularPullback, Functor.singularCochainsFunctor,
    Functor.simplicialCochainsFunctor, HomologicalComplex.unopFunctor, F] using
    (congrArg (fun z => z.f n) h).symm

/-- Singular cohomology with a restricted coefficient module is the restricted
module of ordinary singular cohomology. This is induced by the cochain comparison
and exactness of restriction of scalars. -/
def singularCohomologyRestrictScalarsIso (f : R →+* S)
    (M : ModuleCat.{0} S) (X : TopCat.{0}) (n : ℕ) :
    Basic.singularCohomology ((ModuleCat.restrictScalars f).obj M) X n ≅
      (ModuleCat.restrictScalars f).obj (Basic.singularCohomology M X n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n).mapIso
      (singularCochainsRestrictScalarsIso f M X).symm ≪≫
    ((Basic.singularCochains M X).sc n).mapHomologyIso (ModuleCat.restrictScalars f)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cohomology comparison commutes with pullback by continuous maps. -/
theorem singularCohomologyRestrictScalarsIso_naturality (f : R →+* S)
    (M : ModuleCat.{0} S) {X Y : TopCat.{0}} (g : X ⟶ Y) (n : ℕ) :
    Functor.singularCohomologyPullback ((ModuleCat.restrictScalars f).obj M) g n ≫
        (singularCohomologyRestrictScalarsIso f M X n).hom =
      (singularCohomologyRestrictScalarsIso f M Y n).hom ≫
        (ModuleCat.restrictScalars f).map (Functor.singularCohomologyPullback M g n) := by
  let F := ModuleCat.restrictScalars.{0} f
  let FX := singularCochainsRestrictScalarsIso f M X
  let FY := singularCochainsRestrictScalarsIso f M Y
  have hci : Functor.singularPullback (F.obj M) g ≫ FX.inv =
      FY.inv ≫ (F.mapHomologicalComplex (ComplexShape.up ℕ)).map
        (Functor.singularPullback M g) := by
    apply (cancel_mono FX.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [show (F.mapHomologicalComplex (ComplexShape.up ℕ)).map
        (Functor.singularPullback M g) ≫ FX.hom = FY.hom ≫ Functor.singularPullback (F.obj M) g from
      singularCochainsRestrictScalarsIso_naturality f M g]
    simp
  have hb := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{0} S)
      (ComplexShape.up ℕ) n).map (Functor.singularPullback M g)) F
  change HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (Functor.singularPullback M g)) n ≫
        (((Basic.singularCochains M X).sc n).mapHomologyIso F).hom =
      (((Basic.singularCochains M Y).sc n).mapHomologyIso F).hom ≫
        F.map (HomologicalComplex.homologyMap (Functor.singularPullback M g) n) at hb
  change HomologicalComplex.homologyMap (Functor.singularPullback (F.obj M) g) n ≫
      (HomologicalComplex.homologyMap FX.inv n ≫
        (((Basic.singularCochains M X).sc n).mapHomologyIso F).hom) =
    (HomologicalComplex.homologyMap FY.inv n ≫
        (((Basic.singularCochains M Y).sc n).mapHomologyIso F).hom) ≫
      F.map (HomologicalComplex.homologyMap (Functor.singularPullback M g) n)
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp, hci,
    HomologicalComplex.homologyMap_comp, Category.assoc, hb, Category.assoc]

end

end OAI.AlgebraicTopology.Cohomology.Singular.Chains
