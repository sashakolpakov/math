import OAI.AlgebraicTopology.Cohomology.Singular.Formulas
import OAI.AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf
import OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf
import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels

/-! # Augmentation -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.Augmentation

noncomputable section

/-!
# The locally constant augmentation of singular cochains

A locally constant function defines a singular zero-cochain by evaluation at
the point represented by a zero-simplex. Its coboundary vanishes. Conversely,
on a locally path-connected space, every singular zero-cocycle arises uniquely
in this way. These maps commute with restriction to open subsets.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section

variable {R : Type} [Ring R]

/-- Singular zero-cochains are all functions on the points of the space. -/
def singularZeroCochainPointIso (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    (Basic.singularCochains M X).X 0 ≅ ModuleCat.of R (X → M) :=
  Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M 0 ≪≫
    (LinearEquiv.piCongrLeft' R (fun _ : (TopCat.toSSet.obj X) _⦋0⦌ => M)
      TopCat.toSSetObj₀Equiv).toModuleIso

/-- The function coordinate is evaluation on the constant zero-simplex. -/
@[simp]
theorem singularZeroCochainPointIso_apply (M : ModuleCat.{0} R) (X : TopCat.{0})
    (c : (Basic.singularCochains M X).X 0) (x : X) :
    (singularZeroCochainPointIso M X).hom c x =
      (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M 0).hom c
        (TopCat.toSSetObj₀Equiv.symm x) := rfl

@[simp]
theorem singularZeroCochainPointIso_apply_simplex (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (c : (Basic.singularCochains M X).X 0)
    (s : (TopCat.toSSet.obj X) _⦋0⦌) :
    (singularZeroCochainPointIso M X).hom c (TopCat.toSSetObj₀Equiv s) =
      (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M 0).hom c s := by
  rw [singularZeroCochainPointIso_apply, Equiv.symm_apply_apply]

/-- In degree zero, the singular coboundary is endpoint value minus starting value. -/
theorem singularZeroCoboundary_apply (M : ModuleCat.{0} R) (X : TopCat.{0})
    (c : (Basic.singularCochains M X).X 0) (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M 1).hom
        ((Basic.singularCochains M X).d 0 1 c) s =
      (singularZeroCochainPointIso M X).hom c
          (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj X).δ 0 s)) -
        (singularZeroCochainPointIso M X).hom c
          (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj X).δ 1 s)) := by
  rw [Formulas.degreewiseFunctionIso_coboundary]
  change (∑ i : Fin 2, ((-1 : ℤ) ^ i.val) •
    (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M 0).hom c
      ((TopCat.toSSet.obj X).δ i s)) = _
  rw [Fin.sum_univ_two, singularZeroCochainPointIso_apply_simplex,
    singularZeroCochainPointIso_apply_simplex]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one,
    pow_one, neg_one_zsmul, sub_eq_add_neg]

/-- Zero singular coboundary means that the associated point function is
constant along every path. This statement holds without local hypotheses. -/
theorem singularZeroCoboundary_eq_zero_iff (M : ModuleCat.{0} R) (X : TopCat.{0})
    (c : (Basic.singularCochains M X).X 0) :
    (Basic.singularCochains M X).d 0 1 c = 0 ↔
      ∀ x y : X, Joined x y →
        (singularZeroCochainPointIso M X).hom c x =
          (singularZeroCochainPointIso M X).hom c y := by
  constructor
  · intro hc x y hxy
    obtain ⟨p⟩ := hxy
    let q : X.Path x y := TopCat.pathEquiv.symm p
    have h := singularZeroCoboundary_apply M X c
      (TopCat.toSSetObj₁Equiv.symm q.hom)
    have hz : (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M 1).hom
        ((Basic.singularCochains M X).d 0 1 c) (TopCat.toSSetObj₁Equiv.symm q.hom) = 0 := by
      rw [hc, map_zero]
      rfl
    have heq : (singularZeroCochainPointIso M X).hom c y -
        (singularZeroCochainPointIso M X).hom c x = 0 := by
      simpa only [TopCat.δ_zero_toSSetObj₁Equiv.symm,
        TopCat.δ_one_toSSetObj₁Equiv.symm, Equiv.apply_symm_apply,
        TopCat.Path.hom₀, TopCat.Path.hom₁] using h.symm.trans hz
    exact (sub_eq_zero.mp heq).symm
  · intro hc
    apply (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M 1).toLinearEquiv.injective
    change (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M 1).hom
      ((Basic.singularCochains M X).d 0 1 c) =
        (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M 1).hom 0
    ext s
    rw [singularZeroCoboundary_apply]
    rw [map_zero]
    change _ - _ = 0
    apply sub_eq_zero.mpr
    apply (hc _ _ ?_).symm
    exact ⟨TopCat.pathEquiv {
      hom := TopCat.toSSetObj₁Equiv s
      hom₀ := TopCat.toSSetObj₁Equiv_apply_zero s
      hom₁ := TopCat.toSSetObj₁Equiv_apply_one s }⟩

/-- Local constancy is equivalent to path invariance on a locally path-connected
space; no topology on the function's codomain is required. -/
theorem isLocallyConstant_iff_pathInvariant (X : TopCat.{0})
    [LocallyPathConnectedSpace X] {Y : Type} (f : X → Y) :
    IsLocallyConstant f ↔ ∀ x y : X, Joined x y → f x = f y := by
  constructor
  · intro hf x y hxy
    obtain ⟨p⟩ := hxy
    simpa only [Function.comp_apply, Path.source, Path.target] using
      (hf.comp_continuous p.continuous).apply_eq_of_preconnectedSpace 0 1
  · intro hf
    apply (IsLocallyConstant.iff_exists_open f).2
    intro x
    exact ⟨pathComponent x, IsOpen.pathComponent x, mem_pathComponent_self x,
      fun y hy => (hf x y hy).symm⟩

/-- A locally constant function defines its literal point-evaluation zero-cochain. -/
def locallyConstantToSingularZero (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    ModuleCat.of R (LocallyConstant X M) ⟶ (Basic.singularCochains M X).X 0 :=
  ModuleCat.ofHom (LocallyConstant.coeFnₗ R) ≫ (singularZeroCochainPointIso M X).inv

/-- The augmentation evaluates a function at the actual point of a zero-simplex. -/
@[simp]
theorem locallyConstantToSingularZero_apply (M : ModuleCat.{0} R) (X : TopCat.{0})
    (f : LocallyConstant X M) (x : X) :
    (singularZeroCochainPointIso M X).hom (locallyConstantToSingularZero M X f) x =
      f x := by
  change ((singularZeroCochainPointIso M X).hom
    ((singularZeroCochainPointIso M X).inv (f : X → M))) x = f x
  rw [Iso.inv_hom_id_apply]

/-- The degree-zero augmentation is injective on every topological space. -/
theorem locallyConstantToSingularZero_injective (M : ModuleCat.{0} R)
    (X : TopCat.{0}) : Function.Injective (locallyConstantToSingularZero M X) := by
  intro f g h
  apply LocallyConstant.ext
  intro x
  exact (locallyConstantToSingularZero_apply M X f x).symm.trans
    ((congrArg (fun c => (singularZeroCochainPointIso M X).hom c x) h).trans
      (locallyConstantToSingularZero_apply M X g x))

/-- Locally constant point functions have zero singular coboundary. -/
theorem locallyConstantToSingularZero_d (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    locallyConstantToSingularZero M X ≫ (Basic.singularCochains M X).d 0 1 = 0 := by
  ext f
  change (Basic.singularCochains M X).d 0 1 (locallyConstantToSingularZero M X f) = 0
  apply (singularZeroCoboundary_eq_zero_iff M X _).2
  intro x y hxy
  rw [locallyConstantToSingularZero_apply, locallyConstantToSingularZero_apply]
  obtain ⟨p⟩ := hxy
  have h : f.toFun x = f.toFun y := by
    simpa only [Function.comp_apply, Path.source, Path.target] using
    (f.isLocallyConstant.comp_continuous p.continuous).apply_eq_of_preconnectedSpace 0 1
  exact h

/-- On a locally path-connected space the image of the augmentation is exactly
the kernel of the actual singular coboundary. -/
theorem locallyConstantToSingularZero_range_eq_ker (M : ModuleCat.{0} R)
    (X : TopCat.{0}) [LocallyPathConnectedSpace X] :
    LinearMap.range (locallyConstantToSingularZero M X).hom =
      LinearMap.ker ((Basic.singularCochains M X).d 0 1).hom := by
  ext c
  constructor
  · rintro ⟨f, rfl⟩
    exact ConcreteCategory.congr_hom (locallyConstantToSingularZero_d M X) f
  · intro hc
    have hf : IsLocallyConstant ((singularZeroCochainPointIso M X).hom c) :=
      (isLocallyConstant_iff_pathInvariant X _).2
        ((singularZeroCoboundary_eq_zero_iff M X c).1 hc)
    refine ⟨⟨(singularZeroCochainPointIso M X).hom c, hf⟩, ?_⟩
    change (singularZeroCochainPointIso M X).inv
      ((singularZeroCochainPointIso M X).hom c) = c
    exact Iso.hom_inv_id_apply (singularZeroCochainPointIso M X) c

/-- Point coordinates of singular zero-cochains commute with continuous pullback. -/
theorem singularZeroCochainPointIso_pullback (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) (c : (Basic.singularCochains M Y).X 0) (x : X) :
    (singularZeroCochainPointIso M X).hom ((Functor.singularPullback M f).f 0 c) x =
      (singularZeroCochainPointIso M Y).hom c (f x) := by
  change (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M 0).hom
      ((Functor.simplicialPullback M (TopCat.toSSet.map f)).f 0 c)
      (TopCat.toSSetObj₀Equiv.symm x) = _
  rw [Formulas.degreewiseFunctionIso_pullback]
  rfl

/-- Pulling back a locally constant function gives the pullback of its
point-evaluation singular cochain. -/
theorem locallyConstantToSingularZero_naturality (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) :
    ModuleCat.ofHom (LocallyConstant.comapₗ R f.hom) ≫
        locallyConstantToSingularZero M X =
      locallyConstantToSingularZero M Y ≫ (Functor.singularPullback M f).f 0 := by
  ext g
  apply (singularZeroCochainPointIso M X).toLinearEquiv.injective
  change (singularZeroCochainPointIso M X).hom
      (locallyConstantToSingularZero M X (LocallyConstant.comapₗ R f.hom g)) =
    (singularZeroCochainPointIso M X).hom
      ((Functor.singularPullback M f).f 0 (locallyConstantToSingularZero M Y g))
  ext x
  rw [locallyConstantToSingularZero_apply, singularZeroCochainPointIso_pullback,
    locallyConstantToSingularZero_apply]
  rfl

/-- The first three terms of the augmented singular cochain sequence. -/
def locallyConstantSingularZeroShortComplex (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    ShortComplex (ModuleCat.{0} R) :=
  ShortComplex.mk (locallyConstantToSingularZero M X)
    ((Basic.singularCochains M X).d 0 1) (locallyConstantToSingularZero_d M X)

/-- The augmented sequence is exact at degree zero on locally path-connected spaces. -/
theorem locallyConstantSingularZeroShortComplex_exact (M : ModuleCat.{0} R)
    (X : TopCat.{0}) [LocallyPathConnectedSpace X] :
    (locallyConstantSingularZeroShortComplex M X).Exact :=
  (ShortComplex.moduleCat_exact_iff_range_eq_ker _).2
    (locallyConstantToSingularZero_range_eq_ker M X)

/-- The augmentation is the actual categorical kernel of the singular
degree-zero coboundary. -/
def locallyConstantToSingularZero_isKernel (M : ModuleCat.{0} R)
    (X : TopCat.{0}) [LocallyPathConnectedSpace X] :
    IsLimit (KernelFork.ofι (locallyConstantToSingularZero M X)
      (locallyConstantToSingularZero_d M X)) := by
  haveI : Mono (locallyConstantSingularZeroShortComplex M X).f :=
    (ModuleCat.mono_iff_injective _).2 (locallyConstantToSingularZero_injective M X)
  exact (locallyConstantSingularZeroShortComplex_exact M X).fIsKernel

end

namespace Comparison

/-- The presheaf augmentation sends a locally constant complex function on an
open set to the singular cochain that evaluates it at points. -/
def locallyConstantSingularAugmentation (X : TopCat.{0}) :
    DeRham.Comparison.LocallyConstantSheaf.locallyConstantPresheaf X ⟶
      DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℂ ℂ) X 0 where
  app U := locallyConstantToSingularZero (ModuleCat.of ℂ ℂ) (TopCat.of U.unop)
  naturality _U _V i :=
    locallyConstantToSingularZero_naturality (ModuleCat.of ℂ ℂ)
      ((Opens.toTopCat X).map i.unop)

/-- The presheaf augmentation has the claimed literal evaluation formula. -/
@[simp]
theorem locallyConstantSingularAugmentation_apply (X : TopCat.{0}) (U : Opens X)
    (f : LocallyConstant U ℂ) (x : U) :
    (singularZeroCochainPointIso (ModuleCat.of ℂ ℂ) (TopCat.of U)).hom
      ((locallyConstantSingularAugmentation X).app (op U) f) x = f x :=
  locallyConstantToSingularZero_apply (ModuleCat.of ℂ ℂ) (TopCat.of U) f x

/-- The augmentation is a monomorphism of presheaves on every topological space. -/
instance locallyConstantSingularAugmentation_mono (X : TopCat.{0}) :
    Mono (locallyConstantSingularAugmentation X) := by
  have (U : (Opens X)ᵒᵖ) : Mono ((locallyConstantSingularAugmentation X).app U) :=
    (ModuleCat.mono_iff_injective _).2
      (locallyConstantToSingularZero_injective (ModuleCat.of ℂ ℂ) (TopCat.of U.unop))
  exact NatTrans.mono_of_mono_app _

/-- The first presheaf coboundary annihilates the locally constant augmentation. -/
theorem locallyConstantSingularAugmentation_d (X : TopCat.{0}) :
    locallyConstantSingularAugmentation X ≫
      (DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℂ ℂ) X).d 0 1 = 0 := by
  apply NatTrans.ext
  funext U
  exact locallyConstantToSingularZero_d (ModuleCat.of ℂ ℂ) (TopCat.of U.unop)

/-- The augmented degree-zero sequence in the category of complex-module-valued presheaves. -/
def singularAugmentationShortComplex (X : TopCat.{0}) :
    ShortComplex (X.Presheaf (ModuleCat.{0} ℂ)) :=
  ShortComplex.mk (locallyConstantSingularAugmentation X)
    ((DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℂ ℂ) X).d 0 1)
    (locallyConstantSingularAugmentation_d X)

/-- On a locally path-connected space, the augmentation is the actual presheaf
kernel of the first singular coboundary. -/
def locallyConstantSingularAugmentation_isKernel (X : TopCat.{0})
    [LocallyPathConnectedSpace X] :
    IsLimit (KernelFork.ofι (locallyConstantSingularAugmentation X)
      (locallyConstantSingularAugmentation_d X)) := by
  apply evaluationJointlyReflectsLimits
  intro U
  refine (isLimitMapConeForkEquiv'
    ((evaluation (Opens X)ᵒᵖ (ModuleCat.{0} ℂ)).obj U)
    (locallyConstantSingularAugmentation_d X)).symm ?_
  haveI : LocallyPathConnectedSpace U.unop := U.unop.isOpen.locallyPathConnectedSpace
  exact locallyConstantToSingularZero_isKernel (ModuleCat.of ℂ ℂ) (TopCat.of U.unop)

/-- Exactness at singular degree zero holds as a presheaf statement, not just
as a collection of unrelated objectwise equalities. -/
theorem singularAugmentationShortComplex_exact (X : TopCat.{0})
    [LocallyPathConnectedSpace X] :
    (singularAugmentationShortComplex X).Exact :=
  (singularAugmentationShortComplex X).exact_of_f_is_kernel
    (locallyConstantSingularAugmentation_isKernel X)

end Comparison

end

end OAI.AlgebraicTopology.Cohomology.Singular.Augmentation
