import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteProperMap
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCap
import OAI.AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Locally Finite Coefficients -/

namespace OAI.AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients

noncomputable section

/-!
# Integer-to-rational coefficients on actual locally finite singular chains

Coefficient casting preserves the spatially locally finite support. Face and
proper-map coefficients are proved finite sums, so casting commutes with them.
The resulting chain map has the actual rational chain complex, restricted to
integer scalars, as its target. No scalar-extension isomorphism is asserted.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set Function
open scoped Simplicial BigOperators

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def lfIntegerLinearOfAdditive {M N : Type*}
    [AddCommGroup M] [AddCommGroup N]
    {modM : Module ℤ M} {modN : Module ℤ N} (f : M →+ N) : M →ₗ[ℤ] N where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    change f (modM.smul r x) = modN.smul r (f x)
    simp only [int_smul_eq_zsmul, map_zsmul]

section Spatial

variable {T ι κ : Type*} [TopologicalSpace T]

/-- Rational casting does not change the nonzero spatial support of integer coefficients. -/
theorem spatiallyLocallyFinite_intCast {image : ι → Set T} {c : ι → ℤ}
    (hc : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.SpatialSupport.IsLocallyFinite image c) :
    AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.SpatialSupport.IsLocallyFinite image (fun i => (c i : ℚ)) := by
  simpa only [AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.SpatialSupport.IsLocallyFinite, Int.cast_ne_zero] using hc

/-- The actual coefficient map on a spatially locally finite module. -/
def spatialIntegralToRational (image : ι → Set T) :
    AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.SpatialSupport.module ℤ image →ₗ[ℤ] AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.SpatialSupport.module ℚ image :=
  lfIntegerLinearOfAdditive
    { toFun c := ⟨fun i => (c i : ℚ), spatiallyLocallyFinite_intCast c.property⟩
      map_zero' := by
        apply Subtype.ext
        funext i
        exact Int.cast_zero
      map_add' c d := by
        apply Subtype.ext
        funext i
        exact Int.cast_add (c i) (d i) }

@[simp]
theorem spatialIntegralToRational_apply (image : ι → Set T)
    (c : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.SpatialSupport.module ℤ image) (i : ι) :
    spatialIntegralToRational image c i = (c i : ℚ) := rfl

theorem spatialIntegralToRational_support (image : ι → Set T)
    (c : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.SpatialSupport.module ℤ image) :
    Function.support (spatialIntegralToRational image c : ι → ℚ) =
      Function.support (c : ι → ℤ) := by
  ext i
  simp only [Function.mem_support, spatialIntegralToRational_apply, Int.cast_ne_zero]

theorem spatialIntegralToRational_injective (image : ι → Set T) :
    Function.Injective (spatialIntegralToRational image) := by
  intro c d h
  apply Subtype.ext
  funext i
  have hi := congrArg (fun z : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.SpatialSupport.module ℚ image => z i) h
  change (c i : ℚ) = (d i : ℚ) at hi
  exact_mod_cast hi

/-- On an actual finite contributing fiber, rational casting commutes with summation. -/
theorem intCast_fiberSum (u : ι → κ) (c : ι → ℤ) (j : κ)
    (hfin : ({i | u i = j} ∩ Function.support c).Finite) :
    ((AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.SpatialSupport.fiberSum u c j : ℤ) : ℚ) =
      AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.SpatialSupport.fiberSum u (fun i => (c i : ℚ)) j :=
  (Int.castAddHom ℚ).map_finsum_mem' hfin

/-- Finite ordinary coefficient functions are sent to their literal rational casts. -/
theorem spatialIntegralToRational_ofFinsupp (image : ι → Set T) (c : ι →₀ ℤ) :
    spatialIntegralToRational image (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp image c) =
      AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp image
        (c.mapRange (Int.castAddHom ℚ) (map_zero (Int.castAddHom ℚ))) := by
  apply Subtype.ext
  funext i
  rfl

end Spatial

/-- Integer-to-rational coefficient casting on genuine locally finite singular chains. -/
abbrev locallyFiniteIntegralToRational (X : TopCat.{0}) (n : ℕ) :
    AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ X n →ₗ[ℤ] AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℚ X n :=
  spatialIntegralToRational (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.singularSimplexImage X n)

@[simp]
theorem locallyFiniteIntegralToRational_apply (X : TopCat.{0}) (n : ℕ)
    (c : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ X n) (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    locallyFiniteIntegralToRational X n c s = (c s : ℚ) := rfl

/-- Casting commutes with every genuine singular face map. -/
theorem locallyFiniteIntegralToRational_face (X : TopCat.{0}) (n : ℕ)
    (i : Fin (n + 2)) (c : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ X (n + 1)) :
    locallyFiniteIntegralToRational X n (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.locallyFiniteFace ℤ X n i c) =
      AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.locallyFiniteFace ℚ X n i (locallyFiniteIntegralToRational X (n + 1) c) := by
  apply Subtype.ext
  funext s
  exact intCast_fiberSum _ _ _ (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.locallyFiniteFace_finite X n i c s)

/-- Compatibility with every differential of the actual locally finite complex. -/
theorem locallyFiniteIntegralToRational_d (X : TopCat.{0}) (i j : ℕ)
    (c : (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X).X i) :
    locallyFiniteIntegralToRational X j ((AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X).d i j c) =
      (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℚ X).d i j (locallyFiniteIntegralToRational X i c) := by
  by_cases hij : (ComplexShape.down ℕ).Rel i j
  · have hi : j + 1 = i := hij
    subst i
    change locallyFiniteIntegralToRational X j
        (((AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X).d (j + 1) j).hom c) =
      ((AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℚ X).d (j + 1) j).hom
        (locallyFiniteIntegralToRational X (j + 1) c)
    rw [AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex_d_int, AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex_d_int]
    change locallyFiniteIntegralToRational X j
        ((∑ k : Fin (j + 2), (-1 : ℤ) ^ k.val • AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.locallyFiniteFace ℤ X j k) c) =
      (∑ k : Fin (j + 2), (-1 : ℤ) ^ k.val • AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.locallyFiniteFace ℚ X j k)
        (locallyFiniteIntegralToRational X (j + 1) c)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul,
      locallyFiniteIntegralToRational_face]
  · rw [(AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X).shape i j hij,
      (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℚ X).shape i j hij]
    exact map_zero _

theorem locallyFiniteIntegralToRational_boundary (X : TopCat.{0}) (n : ℕ)
    (c : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ X (n + 1)) :
    locallyFiniteIntegralToRational X n (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.locallyFiniteBoundary ℤ X n c) =
      AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.locallyFiniteBoundary ℚ X n (locallyFiniteIntegralToRational X (n + 1) c) := by
  have h := locallyFiniteIntegralToRational_d X (n + 1) n c
  change locallyFiniteIntegralToRational X n
      (((AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X).d (n + 1) n).hom c) =
    ((AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℚ X).d (n + 1) n).hom
      (locallyFiniteIntegralToRational X (n + 1) c) at h
  simp only [AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex_d] at h
  exact h

/-- The actual rational locally finite complex, viewed as an integer-module complex. -/
abbrev rationalLocallyFiniteAsIntegral (X : TopCat.{0}) :
    ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  ((ModuleCat.restrictScalars (Int.castRingHom ℚ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℚ X)

/-- The genuine coefficient-change chain map. -/
def locallyFiniteIntegralToRationalChainMap (X : TopCat.{0}) :
    AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X ⟶ rationalLocallyFiniteAsIntegral X where
  f n := ModuleCat.ofHom (X := (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X).X n)
    (Y := (ModuleCat.restrictScalars (Int.castRingHom ℚ)).obj
      ((AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℚ X).X n))
    (lfIntegerLinearOfAdditive (locallyFiniteIntegralToRational X n).toAddMonoidHom)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact (locallyFiniteIntegralToRational_d X i j c).symm

@[simp]
theorem locallyFiniteIntegralToRationalChainMap_f_apply (X : TopCat.{0}) (n : ℕ)
    (c : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ X n) :
    (locallyFiniteIntegralToRationalChainMap X).f n c =
      locallyFiniteIntegralToRational X n c := rfl

/-- Coefficient change commutes with the finite sums defining proper pushforward. -/
theorem locallyFiniteIntegralToRational_proper {X Y : TopCat.{0}}
    (f : X ⟶ Y) (hf : IsProperMap f) (n : ℕ)
    (c : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ X n) :
    locallyFiniteIntegralToRational Y n (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteProperMap.Cycles.locallyFiniteProperMap ℤ f hf n c) =
      AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteProperMap.Cycles.locallyFiniteProperMap ℚ f hf n (locallyFiniteIntegralToRational X n c) := by
  apply Subtype.ext
  funext s
  exact intCast_fiberSum _ _ _ (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteProperMap.Cycles.locallyFiniteProperMap_finite f hf n c s)

@[reassoc]
theorem locallyFiniteIntegralToRationalChainMap_naturality {X Y : TopCat.{0}}
    (f : X ⟶ Y) (hf : IsProperMap f) :
    AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteProperMap.Cycles.locallyFiniteProperChainMap ℤ f hf ≫ locallyFiniteIntegralToRationalChainMap Y =
      locallyFiniteIntegralToRationalChainMap X ≫
        ((ModuleCat.restrictScalars (Int.castRingHom ℚ)).mapHomologicalComplex
          (ComplexShape.down ℕ)).map (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteProperMap.Cycles.locallyFiniteProperChainMap ℚ f hf) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact locallyFiniteIntegralToRational_proper f hf n c

/-- On finite ordinary chains this is exactly the existing integer-to-rational map. -/
theorem locallyFiniteIntegralToRational_ordinary (X : TopCat.{0}) (n : ℕ)
    (c : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    locallyFiniteIntegralToRational X n (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite ℤ X n c) =
      AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite ℚ X n (IntegralCapCoefficients.integralToScalarSingular (R := ℚ) X n c) := by
  have he : (locallyFiniteIntegralToRational X n).comp (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite ℤ X n) =
      ((AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite ℚ X n).restrictScalars ℤ).comp
        (IntegralCapCoefficients.integralToScalarSingular (R := ℚ) X n) := by
    apply Cohomology.Singular.ChainDual.chainFunctional_ext (TopCat.toSSet.obj X)
      (ModuleCat.of ℤ (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℚ X n))
    intro s
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      IntegralCapCoefficients.integralToScalarSingular, IntegralCapCoefficients.integralToScalarSimplicial_simplex,
      AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCap.Cycles.ordinaryToLocallyFinite_simplexChain]
    apply Subtype.ext
    funext t
    change (((Finsupp.single s (1 : ℤ)) t : ℤ) : ℚ) = (Finsupp.single s (1 : ℚ)) t
    classical
    by_cases h : s = t <;> simp [h]
  exact LinearMap.congr_fun he c

/-- The finite-to-locally-finite square is a square of genuine chain maps. -/
theorem locallyFiniteIntegralToRationalChainMap_ordinary (X : TopCat.{0}) :
    AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap ℤ X ≫ locallyFiniteIntegralToRationalChainMap X =
      IntegralCapCoefficients.integralToScalarSingularChainMap (R := ℚ) X ≫
        ((ModuleCat.restrictScalars (Int.castRingHom ℚ)).mapHomologicalComplex
          (ComplexShape.down ℕ)).map (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap ℚ X) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact locallyFiniteIntegralToRational_ordinary X n c

/-- Restriction of scalars preserves the homology of the actual rational complex.
This compares the same rational groups as integer modules; it is not extension of scalars. -/
def locallyFiniteRationalHomologyRestrictIso (X : TopCat.{0}) (n : ℕ) :
    (rationalLocallyFiniteAsIntegral X).homology n ≅
      (ModuleCat.restrictScalars (Int.castRingHom ℚ)).obj
        ((AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℚ X).homology n) :=
  ((AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℚ X).sc n).mapHomologyIso
    (ModuleCat.restrictScalars (Int.castRingHom ℚ))

@[reassoc]
theorem locallyFiniteRationalHomologyRestrictIso_naturality {X Y : TopCat.{0}}
    (f : X ⟶ Y) (hf : IsProperMap f) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((ModuleCat.restrictScalars (Int.castRingHom ℚ)).mapHomologicalComplex
          (ComplexShape.down ℕ)).map (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteProperMap.Cycles.locallyFiniteProperChainMap ℚ f hf)) n ≫
        (locallyFiniteRationalHomologyRestrictIso Y n).hom =
      (locallyFiniteRationalHomologyRestrictIso X n).hom ≫
        (ModuleCat.restrictScalars (Int.castRingHom ℚ)).map
          (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap ℚ f hf n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteProperMap.Cycles.locallyFiniteProperChainMap ℚ f hf))
    (ModuleCat.restrictScalars (Int.castRingHom ℚ))

/-- The induced map into actual rational locally finite homology, with scalar restriction explicit. -/
def locallyFiniteIntegralToRationalHomologyMap (X : TopCat.{0}) (n : ℕ) :
    (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X).homology n ⟶
      (ModuleCat.restrictScalars (Int.castRingHom ℚ)).obj
        ((AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℚ X).homology n) :=
  HomologicalComplex.homologyMap (locallyFiniteIntegralToRationalChainMap X) n ≫
    (locallyFiniteRationalHomologyRestrictIso X n).hom

/-- An integer-linear presentation of the same induced map between the native homology groups. -/
def locallyFiniteIntegralToRationalHomology (X : TopCat.{0}) (n : ℕ) :
    (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X).homology n →ₗ[ℤ]
      (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℚ X).homology n :=
  lfIntegerLinearOfAdditive
    (locallyFiniteIntegralToRationalHomologyMap X n).hom.toAddMonoidHom

@[simp]
theorem locallyFiniteIntegralToRationalHomology_apply (X : TopCat.{0}) (n : ℕ)
    (h : (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X).homology n) :
    locallyFiniteIntegralToRationalHomology X n h =
      locallyFiniteIntegralToRationalHomologyMap X n h := rfl

@[reassoc]
theorem locallyFiniteIntegralToRationalHomologyMap_naturality {X Y : TopCat.{0}}
    (f : X ⟶ Y) (hf : IsProperMap f) (n : ℕ) :
    AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap ℤ f hf n ≫ locallyFiniteIntegralToRationalHomologyMap Y n =
      locallyFiniteIntegralToRationalHomologyMap X n ≫
        (ModuleCat.restrictScalars (Int.castRingHom ℚ)).map
          (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap ℚ f hf n) := by
  simp only [locallyFiniteIntegralToRationalHomologyMap, Category.assoc]
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    locallyFiniteIntegralToRationalChainMap_naturality, HomologicalComplex.homologyMap_comp,
    Category.assoc, locallyFiniteRationalHomologyRestrictIso_naturality]

/-- The elementwise proper-pushforward formula for the actual rationalized homology class. -/
theorem locallyFiniteIntegralToRationalHomology_naturality {X Y : TopCat.{0}}
    (f : X ⟶ Y) (hf : IsProperMap f) (n : ℕ)
    (h : (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X).homology n) :
    AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap ℚ f hf n
        (locallyFiniteIntegralToRationalHomology X n h) =
      locallyFiniteIntegralToRationalHomology Y n
        (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap ℤ f hf n h) := by
  have he := congrArg (fun g => g h)
    (locallyFiniteIntegralToRationalHomologyMap_naturality f hf n)
  exact he.symm

end

end OAI.AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients
