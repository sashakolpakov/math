import OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.CechSequence
import OAI.AlgebraicGeometry.DivisorClass.Chern.SubspaceCechAugmentation

/-! # Cech Is -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.CechIs

noncomputable section

section

/-!
# ChernClass: global relative cochains augment the actual relative Cech complex

Actual subspace restriction commutes with the global singular augmentation.
The kernel universal property then supplies the unique relative cochain map,
and both squares of the ordinary pair sequence commute exactly.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech

variable {I : Type} (X : TopCat.{0}) (A : Set X) (U : I → Opens X)

/-- On each actual induced-cover intersection, both paths restrict the same global cochain. -/
theorem globalSubspaceColumnAugmentation_comm (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n) :
    (SubspaceCechD.RationalCech.subspaceCechColumnMap X A U 0).f n
      (SubspaceCechD.RationalCech.subspaceCechRestriction X A U 0 n
        ((Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X U (ModuleCat.of ℚ ℚ)).f n c)) =
    (Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation (TopCat.of A) (SubspaceCechD.RationalCech.inducedSubspaceCover X A U)
      (ModuleCat.of ℚ ℚ)).f n ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f n c) := by
  funext a
  let f : TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) ⟶ X :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let g := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace A (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))
  let v : TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (SubspaceCechD.RationalCech.inducedSubspaceCover X A U) a) ⟶ TopCat.of A :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have h : AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) f ≫ AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) g ≫
      (SubspaceCechD.RationalCech.subspaceIntersectionCochainIso X A U a).hom =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A ≫ AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) v := by
    change AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) f ≫ AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) g ≫
        AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (SubspaceCechD.RationalCech.subspaceIntersectionIso X A U a).hom =
      AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A) ≫ AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) v
    rw [← AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp, ← AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp, ← AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp]
    rfl
  change (SubspaceCechD.RationalCech.subspaceIntersectionCochainIso X A U a).hom.f n
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace A (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))).f n
        (((Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X U (ModuleCat.of ℚ ℚ)).f n c) a)) = _
  rw [Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation_apply, Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation_apply]
  exact ConcreteCategory.congr_hom (congrArg (fun k => k.f n) h) c

/-- The global augmentation commutes with genuine restriction to the subspace. -/
theorem globalSubspaceCechAugmentation_comm :
    Rational.CechComparison.RationalCech.globalSingularCechAugmentation X U (ModuleCat.of ℚ ℚ) ≫ CechSequence.RationalCech.subspaceCechTotalRestriction X A U =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A ≫ SubspaceCechAugmentation.RationalCech.subspaceCechAugmentation X A U := by
  apply (cancel_mono (SubspaceCechD.RationalCech.subspaceCechTotalIso X A U).hom).mp
  rw [Category.assoc, Category.assoc, SubspaceCechAugmentation.RationalCech.subspaceCechAugmentation_transport]
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  have hmap := CechSequence.RationalCech.cechTotalInclusion_map_apply X U (SubspaceCechD.RationalCech.subspacePresheafRestriction X A) 0 n n (Nat.zero_add n)
    ((Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X U (ModuleCat.of ℚ ℚ)).f n c)
  have htransport := SubspaceCechAugmentation.RationalCech.subspaceCechTotalIso_inclusion X A U 0 n n (Nat.zero_add n)
    (SubspaceCechD.RationalCech.subspaceCechRestriction X A U 0 n
      ((Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X U (ModuleCat.of ℚ ℚ)).f n c))
  change (SubspaceCechD.RationalCech.subspaceCechTotalIso X A U).hom.f n
      ((CechSequence.RationalCech.subspaceCechTotalRestriction X A U).f n
        (Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) 0 n n (Nat.zero_add n)
          ((Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X U (ModuleCat.of ℚ ℚ)).f n c))) =
    Rational.Cech.RationalCech.cechTotalInclusion (SubspaceCechD.RationalCech.inducedSubspaceCover X A U)
      (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) (TopCat.of A)) 0 n n (Nat.zero_add n)
      ((Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation (TopCat.of A) (SubspaceCechD.RationalCech.inducedSubspaceCover X A U)
        (ModuleCat.of ℚ ℚ)).f n ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f n c))
  rw [hmap, htransport, globalSubspaceColumnAugmentation_comm]

/-- The image of a global relative cochain has zero subspace restriction. -/
theorem relativeGlobalCechAugmentation_restriction_zero :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A ≫
      Rational.CechComparison.RationalCech.globalSingularCechAugmentation X U (ModuleCat.of ℚ ℚ)) ≫
        CechSequence.RationalCech.subspaceCechTotalRestriction X A U = 0 := by
  rw [Category.assoc, globalSubspaceCechAugmentation_comm, ← Category.assoc,
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_restriction, zero_comp]

/-- The genuine global relative augmentation, constructed by the actual kernel property. -/
def relativeCechAugmentation :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A ⟶ CechSequence.RationalCech.relativeCechTotal X A U := by
  let hS := CechSequence.RationalCech.relativeCechSequence_shortExact X A U
  have := hS.mono_f
  exact hS.exact.lift
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A ≫
      Rational.CechComparison.RationalCech.globalSingularCechAugmentation X U (ModuleCat.of ℚ ℚ))
    (relativeGlobalCechAugmentation_restriction_zero X A U)

/-- Forgetting support commutes exactly with this relative augmentation. -/
theorem relativeCechAugmentation_inclusion :
    relativeCechAugmentation X A U ≫ CechSequence.RationalCech.relativeCechTotalInclusion X A U =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A ≫
        Rational.CechComparison.RationalCech.globalSingularCechAugmentation X U (ModuleCat.of ℚ ℚ) := by
  let hS := CechSequence.RationalCech.relativeCechSequence_shortExact X A U
  have := hS.mono_f
  exact hS.exact.lift_f _ (relativeGlobalCechAugmentation_restriction_zero X A U)

/-- Both genuine cochain sequences form one commutative diagram. -/
def relativeCechSequenceMap :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainSequence (ModuleCat.of ℚ ℚ) X A ⟶ CechSequence.RationalCech.relativeCechSequence X A U where
  τ₁ := relativeCechAugmentation X A U
  τ₂ := Rational.CechComparison.RationalCech.globalSingularCechAugmentation X U (ModuleCat.of ℚ ℚ)
  τ₃ := SubspaceCechAugmentation.RationalCech.subspaceCechAugmentation X A U
  comm₁₂ := relativeCechAugmentation_inclusion X A U
  comm₂₃ := globalSubspaceCechAugmentation_comm X A U

end RationalCech

end

section

/-!
# ChernClass: comparison with genuine global relative singular cohomology

The five lemma applies to the actual long exact sequences of the two short
exact cochain sequences. The already proved absolute and subspace singular
comparisons therefore identify the global relative cohomology in every
positive degree with the actual relative Cech total cohomology.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open _root_.HomologicalComplex _root_.HomologicalComplex.HomologySequence
open _root_.CategoryTheory.ComposableArrows _root_.CategoryTheory.Abelian

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section

/-- The five lemma for the first term of actual short exact cochain sequences,
in a positive cohomological degree. -/
theorem shortExact_isIso_first_succ
    {S T : ShortComplex (CochainComplex (ModuleCat.{0} ℚ) ℕ)} (φ : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact) (h₂ : QuasiIso φ.τ₂) (h₃ : QuasiIso φ.τ₃) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap φ.τ₁ (n + 1)) := by
  let ψ := δ₀Functor.map (mapComposableArrows₅ φ hS hT n (n + 1) rfl)
  have h := isIso_of_epi_of_isIso_of_isIso_of_mono
    (composableArrows₅_exact hS n (n + 1) rfl).δ₀
    (composableArrows₅_exact hT n (n + 1) rfl).δ₀ ψ
    (show Epi (HomologicalComplex.homologyMap φ.τ₂ n) from inferInstance)
    (show IsIso (HomologicalComplex.homologyMap φ.τ₃ n) from inferInstance)
    (show IsIso (HomologicalComplex.homologyMap φ.τ₂ (n + 1)) from inferInstance)
    (show Mono (HomologicalComplex.homologyMap φ.τ₃ (n + 1)) from inferInstance)
  exact h

end

namespace RationalCech

variable {I : Type} (X : TopCat.{0}) (A : Set X) (U : I → Opens X)
variable (hU : ∀ x : X, ∃ i, x ∈ U i)

include hU in
/-- The actual relative augmentation induces an isomorphism in every positive degree. -/
theorem relativeCechAugmentation_isIso_homology_succ (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (relativeCechAugmentation X A U) (n + 1)) :=
  shortExact_isIso_first_succ (relativeCechSequenceMap X A U)
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainSequence_shortExact (ModuleCat.of ℚ ℚ) X A)
    (CechSequence.RationalCech.relativeCechSequence_shortExact X A U)
    (Rational.CechComparison.RationalCech.rationalGlobalSingularCechAugmentation_quasiIso X U hU)
    (SubspaceCechAugmentation.RationalCech.subspaceCechAugmentation_quasiIso X A U hU) n

/-- The comparison is the one induced by the actual global relative cochain augmentation. -/
def relativeCechCohomologyIso (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A (n + 1) ≅
      (CechSequence.RationalCech.relativeCechTotal X A U).homology (n + 1) := by
  have := relativeCechAugmentation_isIso_homology_succ X A U hU n
  exact asIso (HomologicalComplex.homologyMap (relativeCechAugmentation X A U) (n + 1))

theorem relativeCechCohomologyIso_hom (n : ℕ) :
    (relativeCechCohomologyIso X A U hU n).hom =
      HomologicalComplex.homologyMap (relativeCechAugmentation X A U) (n + 1) := rfl

/-- Both comparisons commute with the original forget-support map. -/
theorem relativeCechCohomologyIso_inclusion (n : ℕ) :
    (relativeCechCohomologyIso X A U hU n).hom ≫
        HomologicalComplex.homologyMap (CechSequence.RationalCech.relativeCechTotalInclusion X A U) (n + 1) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X A (n + 1) ≫
        (Rational.CechComparison.RationalCech.singularCechCohomologyIso X U hU (n + 1)).hom := by
  rw [relativeCechCohomologyIso_hom, Rational.CechComparison.RationalCech.singularCechCohomologyIso_hom,
    ← HomologicalComplex.homologyMap_comp, relativeCechAugmentation_inclusion,
    HomologicalComplex.homologyMap_comp]

end RationalCech

end

/-!
# ChernClass: local restrictions of the genuine relative Cech comparison

Projection to Cech degree zero is a cochain map. Evaluating at a singleton
intersection gives the actual relative cochain complex there. Composing
with the global augmentation is the ordinary restriction of pairs.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech

/-- Projection to the zeroth Cech column is an actual cochain map. -/
def zeroColumnProjection
    (K : HomologicalComplex₂ (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)) :
    K.total (ComplexShape.up ℕ) ⟶ K.X 0 where
  f n := AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal K 0 n n (Nat.zero_add n)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    exact (AlgebraicTopology.DeRham.Comparison.DoubleComplexDifferential.DoubleComplex.d_πTotal_zero_succ K i i (Nat.zero_add (i + 1))).symm

variable {I : Type} (X : TopCat.{0}) (A : Set X) (U : I → Opens X)

/-- Evaluate the actual relative zeroth column on one singleton intersection. -/
def relativeCechColumnEvaluation (a : Fin 1 → I) :
    (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativePresheafComplex (ModuleCat.of ℚ ℚ) X A)).X 0 ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace A (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) where
  f _n := ModuleCat.ofHom {
    toFun := fun c => c a
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  comm' _ _ _ := rfl

/-- The actual cochain restriction from the total relative model to a chart. -/
def relativeCechLocalProjection (a : Fin 1 → I) :
    CechSequence.RationalCech.relativeCechTotal X A U ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace A (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) :=
  zeroColumnProjection (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativePresheafComplex (ModuleCat.of ℚ ℚ) X A)) ≫
    relativeCechColumnEvaluation X A U a

/-- Augmenting globally and then taking a local component is the ordinary pair restriction. -/
theorem relativeCechAugmentation_local (a : Fin 1 → I) :
    relativeCechAugmentation X A U ≫ relativeCechLocalProjection X A U a =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ)
        (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a : Set X)) (fun _ hx => hx) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply SubspaceCechD.relativeCochainInclusion_injective (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace A (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) n
  have h := AlgebraicTopology.DeRham.Comparison.DoubleComplexMapComponents.DoubleComplex.project_total_map (Rational.Cech.RationalCech.cechDoubleComplexMap U
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativePresheafInclusion (ModuleCat.of ℚ ℚ) X A)) 0 n n (Nat.zero_add n)
    ((relativeCechAugmentation X A U).f n c)
  change AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)) 0 n n (Nat.zero_add n)
      ((CechSequence.RationalCech.relativeCechTotalInclusion X A U).f n ((relativeCechAugmentation X A U).f n c)) =
    SubspaceCechD.RationalCech.relativeCechInclusion X A U 0 n _ at h
  have hi := ConcreteCategory.congr_hom
    (congrArg (fun f => f.f n) (relativeCechAugmentation_inclusion X A U)) c
  change (CechSequence.RationalCech.relativeCechTotalInclusion X A U).f n ((relativeCechAugmentation X A U).f n c) =
    (Rational.CechComparison.RationalCech.globalSingularCechAugmentation X U (ModuleCat.of ℚ ℚ)).f n
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f n c) at hi
  rw [hi] at h
  have hz := AlgebraicTopology.DeRham.Comparison.DoubleComplexAugmentation.DoubleComplex.πTotal_augmentationToTotal_apply
    (Rational.CechComparison.RationalCech.singularCechDoubleComplex X U (ModuleCat.of ℚ ℚ))
    (Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X U (ModuleCat.of ℚ ℚ))
    (Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation_horizontal X U (ModuleCat.of ℚ ℚ)) n
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f n c)
  change AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)) 0 n n (Nat.zero_add n)
      ((Rational.CechComparison.RationalCech.globalSingularCechAugmentation X U (ModuleCat.of ℚ ℚ)).f n
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f n c)) = _ at hz
  rw [hz] at h
  have ha := congrFun h a
  rw [Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation_apply] at ha
  have hn := ConcreteCategory.congr_hom
    (congrArg (fun f => f.f n) (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a : Set X)) (fun _ hx => hx))) c
  exact ha.symm.trans hn.symm

end RationalCech

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.CechIs
