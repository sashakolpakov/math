import OAI.AlgebraicTopology.Cohomology.Singular.RelativeSequence

/-! # Relative Cochain Triple -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainTriple.Cohomology

noncomputable section

/-!
# The genuine relative cochain sequence of a nested triple

For B ⊆ A ⊆ X, relative cochains are the existing kernels of actual singular
cochain restriction maps. The maps below give the short exact sequence
0 → C*(X,A) → C*(X,B) → C*(A,B) → 0. Inside A the subset B is represented by
the literal inverse image of B under the inclusion A → X.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [Ring R]

/-- The smaller ambient subset, regarded as an actual subset of A. -/
def relativeTripleSubspace (X : TopCat.{0}) (A B : Set X) : Set (TopCat.of A) :=
  {a | a.val ∈ B}

/-- The canonical map from B to its representation as a subset of A. -/
def relativeTripleSubspaceLift (X : TopCat.{0}) (A B : Set X) (hBA : B ⊆ A) :
    TopCat.of B ⟶ TopCat.of (relativeTripleSubspace X A B) :=
  TopCat.ofHom ⟨fun b => ⟨⟨b.val, hBA b.property⟩, b.property⟩,
    (continuous_subtype_val.subtype_mk fun b => hBA b.property).subtype_mk
      fun b => b.property⟩

@[reassoc]
theorem relativeTripleSubspaceLift_inclusions (X : TopCat.{0}) (A B : Set X)
    (hBA : B ⊆ A) :
    relativeTripleSubspaceLift X A B hBA ≫
        LocalHomology.Cycles.subspaceInclusion (TopCat.of A) (relativeTripleSubspace X A B) ≫
          LocalHomology.Cycles.subspaceInclusion X A = LocalHomology.Cycles.subspaceInclusion X B := rfl

/-- Restricting through A and the embedded copy of B is restriction to B. -/
@[reassoc]
theorem subspaceCochainRestriction_triple (M : ModuleCat.{0} R) (X : TopCat.{0})
    (A B : Set X) (hBA : B ⊆ A) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M (TopCat.of A) (relativeTripleSubspace X A B) ≫
          AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (relativeTripleSubspaceLift X A B hBA) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X B := by
  change AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (LocalHomology.Cycles.subspaceInclusion X A) ≫
      AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M
        (LocalHomology.Cycles.subspaceInclusion (TopCat.of A) (relativeTripleSubspace X A B)) ≫
      AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (relativeTripleSubspaceLift X A B hBA) = _
  rw [← AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp, ← AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp]
  rfl

/-- Forget vanishing on A while retaining vanishing on its subset B. -/
def relativeCochainTripleInclusion (M : ModuleCat.{0} R) (X : TopCat.{0})
    (A B : Set X) (hBA : B ⊆ A) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A ⟶ AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X B :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M (𝟙 X) (A := B) (B := A) (fun _ hx => hBA hx)

/-- The actual pair pullback induced by A → X. -/
def relativeCochainTripleRestriction (M : ModuleCat.{0} R) (X : TopCat.{0})
    (A B : Set X) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X B ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M (TopCat.of A) (relativeTripleSubspace X A B) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M (LocalHomology.Cycles.subspaceInclusion X A)
    (A := relativeTripleSubspace X A B) (B := B) (fun _ hx => hx)

@[reassoc (attr := simp)]
theorem relativeCochainTripleInclusion_inclusion (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A B : Set X) (hBA : B ⊆ A) :
    relativeCochainTripleInclusion M X A B hBA ≫ AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X B =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A := by
  simp only [relativeCochainTripleInclusion, AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality,
    AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_id, Category.comp_id]

@[reassoc (attr := simp)]
theorem relativeCochainTripleRestriction_inclusion (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A B : Set X) :
    relativeCochainTripleRestriction M X A B ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M (TopCat.of A) (relativeTripleSubspace X A B) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X B ≫ AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality M (LocalHomology.Cycles.subspaceInclusion X A)
    (fun _ hx => hx)

@[simp]
theorem relativeCochainTripleInclusion_inclusion_apply (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A B : Set X) (hBA : B ⊆ A) (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X B).f n
        ((relativeCochainTripleInclusion M X A B hBA).f n c) =
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n c :=
  ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (relativeCochainTripleInclusion_inclusion M X A B hBA) n) c

@[simp]
theorem relativeCochainTripleRestriction_inclusion_apply (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A B : Set X) (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X B).X n) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M (TopCat.of A) (relativeTripleSubspace X A B)).f n
        ((relativeCochainTripleRestriction M X A B).f n c) =
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f n
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X B).f n c) :=
  ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (relativeCochainTripleRestriction_inclusion M X A B) n) c

instance relativeCochainTripleInclusion_mono (M : ModuleCat.{0} R) (X : TopCat.{0})
    (A B : Set X) (hBA : B ⊆ A) :
    Mono (relativeCochainTripleInclusion M X A B hBA) :=
  mono_of_mono_fac (relativeCochainTripleInclusion_inclusion M X A B hBA)

@[reassoc (attr := simp)]
theorem relativeCochainTripleInclusion_restriction (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A B : Set X) (hBA : B ⊆ A) :
    relativeCochainTripleInclusion M X A B hBA ≫
      relativeCochainTripleRestriction M X A B = 0 := by
  apply (cancel_mono
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M (TopCat.of A) (relativeTripleSubspace X A B))).1
  rw [Category.assoc, relativeCochainTripleRestriction_inclusion,
    ← Category.assoc, relativeCochainTripleInclusion_inclusion,
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_restriction, zero_comp]

/-- The actual relative cochain sequence associated with B ⊆ A ⊆ X. -/
def relativeCochainTripleSequence (M : ModuleCat.{0} R) (X : TopCat.{0})
    (A B : Set X) (hBA : B ⊆ A) :
    ShortComplex (CochainComplex (ModuleCat.{0} R) ℕ) :=
  ShortComplex.mk (relativeCochainTripleInclusion M X A B hBA)
    (relativeCochainTripleRestriction M X A B)
    (relativeCochainTripleInclusion_restriction M X A B hBA)

/-- Exactness in each degree follows from the actual kernels of restriction. -/
theorem relativeCochainTripleSequence_degreewiseExact (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A B : Set X) (hBA : B ⊆ A) (n : ℕ) :
    ((relativeCochainTripleSequence M X A B hBA).map
      (HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.up ℕ) n)).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).2
  intro c hc
  change (relativeCochainTripleRestriction M X A B).f n c = 0 at hc
  have hz : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f n
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X B).f n c) = 0 := by
    rw [← relativeCochainTripleRestriction_inclusion_apply, hc, map_zero]
  have hr : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X B).f n c ∈
      LinearMap.range ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n).hom := by
    rw [AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_range]
    exact hz
  obtain ⟨a, ha⟩ := hr
  refine ⟨a, ?_⟩
  apply (ModuleCat.mono_iff_injective ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X B).f n)).1
    inferInstance
  change (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X B).f n
    ((relativeCochainTripleInclusion M X A B hBA).f n a) = _
  rw [relativeCochainTripleInclusion_inclusion_apply]
  exact ha

/-- The restriction to (A,B) is surjective in each degree: extend its
underlying cochain to X, then use B ⊆ A to prove that extension vanishes on B. -/
theorem relativeCochainTripleRestriction_surjective (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A B : Set X) (hBA : B ⊆ A) (n : ℕ) :
    Function.Surjective ((relativeCochainTripleRestriction M X A B).f n) := by
  intro c
  obtain ⟨a, ha⟩ :=
    (ModuleCat.epi_iff_surjective ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f n)).1
      inferInstance ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M (TopCat.of A)
        (relativeTripleSubspace X A B)).f n c)
  have hzero : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M (TopCat.of A)
      (relativeTripleSubspace X A B)).f n
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M (TopCat.of A)
          (relativeTripleSubspace X A B)).f n c) = 0 :=
    ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_restriction M (TopCat.of A)
        (relativeTripleSubspace X A B)) n) c
  have hz : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X B).f n a = 0 := by
    have h := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
      (subspaceCochainRestriction_triple M X A B hBA) n) a
    change (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (relativeTripleSubspaceLift X A B hBA)).f n
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M (TopCat.of A) (relativeTripleSubspace X A B)).f n
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f n a)) =
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X B).f n a at h
    rw [← h, ha, hzero, map_zero]
  have hr : a ∈ LinearMap.range ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X B).f n).hom := by
    rw [AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_range]
    exact hz
  obtain ⟨b, hb⟩ := hr
  refine ⟨b, ?_⟩
  apply (ModuleCat.mono_iff_injective
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M (TopCat.of A) (relativeTripleSubspace X A B)).f n)).1
      inferInstance
  rw [relativeCochainTripleRestriction_inclusion_apply, hb, ha]

/-- The relative cochain sequence is short exact in every degree. -/
theorem relativeCochainTripleSequence_degreewiseShortExact (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A B : Set X) (hBA : B ⊆ A) (n : ℕ) :
    ((relativeCochainTripleSequence M X A B hBA).map
      (HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.up ℕ) n)).ShortExact where
  exact := relativeCochainTripleSequence_degreewiseExact M X A B hBA n
  mono_f := by
    change Mono ((relativeCochainTripleInclusion M X A B hBA).f n)
    infer_instance
  epi_g := (ModuleCat.epi_iff_surjective _).2
    (relativeCochainTripleRestriction_surjective M X A B hBA n)

/-- The genuine short exact sequence
0 → C*(X,A;M) → C*(X,B;M) → C*(A,B;M) → 0. -/
theorem relativeCochainTripleSequence_shortExact (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A B : Set X) (hBA : B ⊆ A) :
    (relativeCochainTripleSequence M X A B hBA).ShortExact :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact _).2
    (relativeCochainTripleSequence_degreewiseShortExact M X A B hBA)

/-- The actual map H^n(X,A) → H^n(X,B). -/
abbrev relativeCohomologyTripleInclusion (M : ModuleCat.{0} R) (X : TopCat.{0})
    (A B : Set X) (hBA : B ⊆ A) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A n ⟶ AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X B n :=
  HomologicalComplex.homologyMap (relativeCochainTripleInclusion M X A B hBA) n

/-- The actual restriction H^n(X,B) → H^n(A,B). -/
abbrev relativeCohomologyTripleRestriction (M : ModuleCat.{0} R) (X : TopCat.{0})
    (A B : Set X) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X B n ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of A) (relativeTripleSubspace X A B) n :=
  HomologicalComplex.homologyMap (relativeCochainTripleRestriction M X A B) n

/-- The canonical connecting map H^n(A,B) → H^(n+1)(X,A). -/
def relativeCohomologyTripleConnecting (M : ModuleCat.{0} R) (X : TopCat.{0})
    (A B : Set X) (hBA : B ⊆ A) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of A) (relativeTripleSubspace X A B) n ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A (n + 1) :=
  (relativeCochainTripleSequence_shortExact M X A B hBA).δ n (n + 1) rfl

@[reassoc (attr := simp)]
theorem relativeCohomologyTripleInclusion_restriction (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A B : Set X) (hBA : B ⊆ A) (n : ℕ) :
    relativeCohomologyTripleInclusion M X A B hBA n ≫
      relativeCohomologyTripleRestriction M X A B n = 0 := by
  change HomologicalComplex.homologyMap (relativeCochainTripleInclusion M X A B hBA) n ≫
    HomologicalComplex.homologyMap (relativeCochainTripleRestriction M X A B) n = 0
  rw [← HomologicalComplex.homologyMap_comp, relativeCochainTripleInclusion_restriction,
    HomologicalComplex.homologyMap_zero]

@[reassoc (attr := simp)]
theorem relativeCohomologyTripleRestriction_connecting (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A B : Set X) (hBA : B ⊆ A) (n : ℕ) :
    relativeCohomologyTripleRestriction M X A B n ≫
      relativeCohomologyTripleConnecting M X A B hBA n = 0 :=
  (relativeCochainTripleSequence_shortExact M X A B hBA).comp_δ n (n + 1) rfl

@[reassoc (attr := simp)]
theorem relativeCohomologyTripleConnecting_inclusion (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A B : Set X) (hBA : B ⊆ A) (n : ℕ) :
    relativeCohomologyTripleConnecting M X A B hBA n ≫
      relativeCohomologyTripleInclusion M X A B hBA (n + 1) = 0 :=
  (relativeCochainTripleSequence_shortExact M X A B hBA).δ_comp n (n + 1) rfl

/-- Exactness at H^n(X,B) in the long exact sequence of the actual triple. -/
theorem relativeCohomologyTriple_exact_middle (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A B : Set X) (hBA : B ⊆ A) (n : ℕ) :
    (ShortComplex.mk (relativeCohomologyTripleInclusion M X A B hBA n)
      (relativeCohomologyTripleRestriction M X A B n)
      (relativeCohomologyTripleInclusion_restriction M X A B hBA n)).Exact :=
  (relativeCochainTripleSequence_shortExact M X A B hBA).homology_exact₂ n

/-- Exactness at H^n(A,B) in the long exact sequence of the actual triple. -/
theorem relativeCohomologyTriple_exact_target (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A B : Set X) (hBA : B ⊆ A) (n : ℕ) :
    (ShortComplex.mk (relativeCohomologyTripleRestriction M X A B n)
      (relativeCohomologyTripleConnecting M X A B hBA n)
      (relativeCohomologyTripleRestriction_connecting M X A B hBA n)).Exact :=
  (relativeCochainTripleSequence_shortExact M X A B hBA).homology_exact₃ n (n + 1) rfl

/-- Exactness at H^(n+1)(X,A) in the long exact sequence of the actual triple. -/
theorem relativeCohomologyTriple_exact_sourceSucc (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A B : Set X) (hBA : B ⊆ A) (n : ℕ) :
    (ShortComplex.mk (relativeCohomologyTripleConnecting M X A B hBA n)
      (relativeCohomologyTripleInclusion M X A B hBA (n + 1))
      (relativeCohomologyTripleConnecting_inclusion M X A B hBA n)).Exact :=
  (relativeCochainTripleSequence_shortExact M X A B hBA).homology_exact₁ n (n + 1) rfl

/-- Vanishing of both outer groups forces vanishing of H^n(X,B). This is
the induction step for a finite filtration by closed supports. -/
theorem relativeCohomologyTriple_isZero_middle (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A B : Set X) (hBA : B ⊆ A) (n : ℕ)
    (hfirst : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A n))
    (hthird : IsZero
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of A) (relativeTripleSubspace X A B) n)) :
    IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X B n) :=
  (relativeCohomologyTriple_exact_middle M X A B hBA n).isZero_X₂
    (hfirst.eq_of_src _ _) (hthird.eq_of_tgt _ _)

/-- If the adjacent groups H^n(X,A) and H^(n+1)(X,A) vanish, the actual
restriction H^n(X,B) → H^n(A,B) is an isomorphism. -/
theorem relativeCohomologyTripleRestriction_isIso (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A B : Set X) (hBA : B ⊆ A) (n : ℕ)
    (hi : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A n))
    (hj : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A (n + 1))) :
    IsIso (relativeCohomologyTripleRestriction M X A B n) := by
  let : Mono (relativeCohomologyTripleRestriction M X A B n) :=
    (relativeCohomologyTriple_exact_middle M X A B hBA n).mono_g (hi.eq_of_src _ _)
  let : Epi (relativeCohomologyTripleRestriction M X A B n) :=
    (relativeCohomologyTriple_exact_target M X A B hBA n).epi_f (hj.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- The isomorphism is the actual restriction map, so its inverse provides
canonical extension once the two vanishing results have been proved. -/
def relativeCohomologyTripleRestrictionIso (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A B : Set X) (hBA : B ⊆ A) (n : ℕ)
    (hi : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A n))
    (hj : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A (n + 1))) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X B n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of A) (relativeTripleSubspace X A B) n := by
  let := relativeCohomologyTripleRestriction_isIso M X A B hBA n hi hj
  exact asIso (relativeCohomologyTripleRestriction M X A B n)

@[simp]
theorem relativeCohomologyTripleRestrictionIso_hom (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A B : Set X) (hBA : B ⊆ A) (n : ℕ)
    (hi : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A n))
    (hj : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A (n + 1))) :
    (relativeCohomologyTripleRestrictionIso M X A B hBA n hi hj).hom =
      relativeCohomologyTripleRestriction M X A B n := rfl

/-- Canonical extension along the actual restriction isomorphism. -/
abbrev relativeCohomologyTripleExtension (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A B : Set X) (hBA : B ⊆ A) (n : ℕ)
    (hi : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A n))
    (hj : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A (n + 1))) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of A) (relativeTripleSubspace X A B) n ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X B n :=
  (relativeCohomologyTripleRestrictionIso M X A B hBA n hi hj).inv

@[reassoc (attr := simp)]
theorem relativeCohomologyTripleExtension_restriction (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A B : Set X) (hBA : B ⊆ A) (n : ℕ)
    (hi : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A n))
    (hj : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A (n + 1))) :
    relativeCohomologyTripleExtension M X A B hBA n hi hj ≫
      relativeCohomologyTripleRestriction M X A B n = 𝟙 _ :=
  (relativeCohomologyTripleRestrictionIso M X A B hBA n hi hj).inv_hom_id

@[reassoc (attr := simp)]
theorem relativeCohomologyTripleRestriction_extension (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A B : Set X) (hBA : B ⊆ A) (n : ℕ)
    (hi : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A n))
    (hj : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A (n + 1))) :
    relativeCohomologyTripleRestriction M X A B n ≫
      relativeCohomologyTripleExtension M X A B hBA n hi hj = 𝟙 _ :=
  (relativeCohomologyTripleRestrictionIso M X A B hBA n hi hj).hom_inv_id

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainTriple.Cohomology
