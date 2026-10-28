import OAI.AlgebraicTopology.Cohomology.Singular.Contractible
import OAI.AlgebraicTopology.Cohomology.Singular.Augmentation
import OAI.Analysis.DifferentialForms.Manifold.CochainAugmentation
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-! # Convex Resolution -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ConvexResolution

noncomputable section

/-!
# The actual locally constant resolution on convex domains

Point evaluation defines a map from locally constant functions, concentrated
in degree zero, to genuine singular cochains. On a convex subset of a real
normed space this map is a quasi-isomorphism, including when the subset is
empty. Finite intersections in a convex open family therefore satisfy the
same local comparison without a nonemptiness hypothesis.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [Ring R]

/-- The literal locally constant point-evaluation augmentation, as a map from
the actual complex concentrated in degree zero. -/
def locallyConstantSingularResolutionMap (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    (CochainComplex.single₀ (ModuleCat.{0} R)).obj
      (ModuleCat.of R (LocallyConstant X M)) ⟶ Basic.singularCochains M X :=
  (CochainComplex.fromSingle₀Equiv (Basic.singularCochains M X)
    (ModuleCat.of R (LocallyConstant X M))).symm
      ⟨Augmentation.locallyConstantToSingularZero M X, Augmentation.locallyConstantToSingularZero_d M X⟩

@[simp]
theorem locallyConstantSingularResolutionMap_f_zero (M : ModuleCat.{0} R)
    (X : TopCat.{0}) :
    (locallyConstantSingularResolutionMap M X).f 0 = Augmentation.locallyConstantToSingularZero M X :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- The augmentation commutes with actual continuous pullback. -/
@[reassoc]
theorem locallyConstantSingularResolutionMap_naturality (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (CochainComplex.single₀ (ModuleCat.{0} R)).map
        (ModuleCat.ofHom (LocallyConstant.comapₗ R f.hom)) ≫
        locallyConstantSingularResolutionMap M X =
      locallyConstantSingularResolutionMap M Y ≫ Functor.singularPullback M f := by
  apply (CochainComplex.fromSingle₀Equiv (Basic.singularCochains M X)
    (ModuleCat.of R (LocallyConstant Y M))).injective
  apply Subtype.ext
  change ((CochainComplex.single₀ (ModuleCat.{0} R)).map
    (ModuleCat.ofHom (LocallyConstant.comapₗ R f.hom))).f 0 ≫
      (locallyConstantSingularResolutionMap M X).f 0 =
    (locallyConstantSingularResolutionMap M Y).f 0 ≫ (Functor.singularPullback M f).f 0
  rw [CochainComplex.single₀_map_f_zero,
    locallyConstantSingularResolutionMap_f_zero, locallyConstantSingularResolutionMap_f_zero]
  exact Augmentation.locallyConstantToSingularZero_naturality M f

/-- The proved degree-zero kernel and positive singular exactness are exactly
the hypotheses needed for the actual augmentation to be a quasi-isomorphism. -/
theorem locallyConstantSingularResolutionMap_quasiIso_of_positiveExactness
    (M : ModuleCat.{0} R) (X : TopCat.{0}) [LocallyPathConnectedSpace X]
    (hX : ∀ n : ℕ, (Basic.singularCochains M X).ExactAt (n + 1)) :
    QuasiIso (locallyConstantSingularResolutionMap M X) :=
  Analysis.DifferentialForms.Manifold.CochainAugmentation.cochainAugmentation_quasiIso (Basic.singularCochains M X)
    (Augmentation.locallyConstantToSingularZero M X) (Augmentation.locallyConstantToSingularZero_d M X)
    (Augmentation.locallyConstantToSingularZero_isKernel M X) hX

/-- On a locally path-connected contractible space, the augmentation is a
quasi-isomorphism of the actual cochain complexes. -/
theorem locallyConstantSingularResolutionMap_quasiIso_of_contractible
    (M : ModuleCat.{0} R) (X : TopCat.{0}) [LocallyPathConnectedSpace X]
    [ContractibleSpace X] : QuasiIso (locallyConstantSingularResolutionMap M X) :=
  locallyConstantSingularResolutionMap_quasiIso_of_positiveExactness M X
    (fun n => Contractible.singularCochains_exactAt_of_contractible M X (n + 1) (Nat.succ_ne_zero n))

section Convex

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Positive singular exactness for every convex subset, allowing the empty set. -/
theorem singularCochains_exactAt_convex (M : ModuleCat.{0} R)
    {s : Set E} (hs : Convex ℝ s) (n : ℕ) :
    (Basic.singularCochains M (TopCat.of s)).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  by_cases hne : s.Nonempty
  · exact Contractible.isZero_singularCohomology_of_convex M hs hne (n + 1) (Nat.succ_ne_zero n)
  · have : IsEmpty s := ⟨fun x => hne ⟨x.val, x.property⟩⟩
    exact Contractible.isZero_singularCohomology_of_totallyDisconnected M (TopCat.of s)
      (n + 1) (Nat.succ_ne_zero n)

/-- Point evaluation is a genuine singular-cochain resolution on any convex
subset of a real normed space, including an empty subset. -/
theorem locallyConstantSingularResolutionMap_quasiIso_convex
    (M : ModuleCat.{0} R) {s : Set E} (hs : Convex ℝ s) :
    QuasiIso (locallyConstantSingularResolutionMap M (TopCat.of s)) := by
  have : LocallyPathConnectedSpace s := hs.locallyPathConnectedSpace
  exact locallyConstantSingularResolutionMap_quasiIso_of_positiveExactness M (TopCat.of s)
    (singularCochains_exactAt_convex M hs)

/-- The local comparison for a convex open domain; no point of the domain is chosen. -/
theorem locallyConstantSingularResolutionMap_quasiIso_convexOpen
    (M : ModuleCat.{0} R) (U : Opens E) (hU : Convex ℝ (U : Set E)) :
    QuasiIso (locallyConstantSingularResolutionMap M (TopCat.of U)) :=
  locallyConstantSingularResolutionMap_quasiIso_convex M hU

/-- Every finite intersection of a convex open family is convex. -/
theorem convex_cechIntersection {J : Type} (U : J → Opens E)
    (hU : ∀ i, Convex ℝ (U i : Set E)) {p : ℕ} (a : Fin (p + 1) → J) :
    Convex ℝ (DeRham.Comparison.SmoothCech.cechIntersection U a : Set E) := by
  change Convex ℝ ((⨅ k, U (a k) : Opens E) : Set E)
  rw [Opens.coe_iInf]
  exact convex_iInter (fun k => hU (a k))

/-- Each actual section map in a Čech column for a convex cover is a
quasi-isomorphism, including the factors indexed by empty intersections. -/
theorem locallyConstantSingularResolutionMap_quasiIso_cechIntersection
    (M : ModuleCat.{0} R) {J : Type} (U : J → Opens E)
    (hU : ∀ i, Convex ℝ (U i : Set E)) {p : ℕ} (a : Fin (p + 1) → J) :
    QuasiIso (locallyConstantSingularResolutionMap M
      (TopCat.of (DeRham.Comparison.SmoothCech.cechIntersection U a))) :=
  locallyConstantSingularResolutionMap_quasiIso_convexOpen M _ (convex_cechIntersection U hU a)

end Convex

/-- The same actual single-degree augmentation in the category of complex
presheaves, for application of the Čech double-complex functor. -/
def locallyConstantSingularPresheafResolutionMap (X : TopCat.{0}) :
    (CochainComplex.single₀ (X.Presheaf (ModuleCat.{0} ℂ))).obj
      (DeRham.Comparison.LocallyConstantSheaf.locallyConstantPresheaf X) ⟶
        DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℂ ℂ) X :=
  (CochainComplex.fromSingle₀Equiv
    (DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℂ ℂ) X)
    (DeRham.Comparison.LocallyConstantSheaf.locallyConstantPresheaf X)).symm
      ⟨Augmentation.Comparison.locallyConstantSingularAugmentation X,
        Augmentation.Comparison.locallyConstantSingularAugmentation_d X⟩

@[simp]
theorem locallyConstantSingularPresheafResolutionMap_f_zero (X : TopCat.{0}) :
    (locallyConstantSingularPresheafResolutionMap X).f 0 =
      Augmentation.Comparison.locallyConstantSingularAugmentation X :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

end

end OAI.AlgebraicTopology.Cohomology.Singular.ConvexResolution
