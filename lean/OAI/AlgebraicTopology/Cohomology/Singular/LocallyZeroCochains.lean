import OAI.AlgebraicTopology.Cohomology.Singular.SheafResolution
import OAI.AlgebraicTopology.Cohomology.Singular.SmallCochainComparison
import OAI.AlgebraicTopology.Cohomology.Singular.NaturalSmallChains
import OAI.AlgebraicTopology.Cohomology.Singular.SurjectiveQuasiIso
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Locally Zero Cochains -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains

noncomputable section

/-!
# Locally zero singular cochains

The canonical map from genuine singular cochains to global sections of their
degreewise sheafification has precisely the locally zero cochains as kernel.
An actual open cover detects a locally zero cochain, and the small-cochain
comparison makes this kernel acyclic over characteristic-zero fields.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open _root_.TopCat.Presheaf

variable {R : Type} [Ring R]

/-- The kernel of the actual sheafification unit consists precisely of
sections which vanish on some neighborhood of each point. -/
theorem sheafificationUnit_eq_zero_iff_locally_zero (X : TopCat.{0})
    (F : X.Presheaf (ModuleCat.{0} R)) (U : Opens X) (s : F.obj (op U)) :
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) F).app (op U) s = 0 ↔
      ∀ (x : X) (_hx : x ∈ U), ∃ (V : Opens X) (_hxV : x ∈ V) (i : V ⟶ U),
        F.map i.op s = 0 := by
  let η := CategoryTheory.toSheafify (Opens.grothendieckTopology X) F
  let G : TopCat.Sheaf (ModuleCat.{0} R) X :=
    (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R)).obj F
  constructor
  · intro hs x hx
    apply (StalkExactnessAt.germ_eq_zero_iff_locally_zero F x U hx s).1
    have : IsIso ((stalkFunctor (ModuleCat.{0} R) x).map η) :=
      stalkFunctor_map_unit_toSheafify_isIso x (ModuleCat.{0} R) F
    apply (ModuleCat.mono_iff_injective ((stalkFunctor (ModuleCat.{0} R) x).map η)).1
      inferInstance
    rw [map_zero, stalkFunctor_map_germ_apply]
    change G.presheaf.germ U x hx (η.app (op U) s) = 0
    rw [show η.app (op U) s = 0 from hs, map_zero]
  · intro hs
    apply section_ext G U (η.app (op U) s) 0
    intro x hx
    have hz := (StalkExactnessAt.germ_eq_zero_iff_locally_zero F x U hx s).2 (hs x hx)
    change G.presheaf.germ U x hx (η.app (op U) s) = G.presheaf.germ U x hx 0
    rw [← stalkFunctor_map_germ_apply, hz, map_zero, map_zero]

/-- Global sections of the actual degreewise sheafification of singular cochains. -/
def singularSheafGlobalSections (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  (((sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R)) ⋙
    (evaluation (Opens X)ᵒᵖ (ModuleCat.{0} R)).obj (op ⊤)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
        (SheafQuasiIso.sheafifiedCochainComplex (DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X))

/-- On the top open subset the sheafification unit is a genuine cochain map. -/
def singularTopSectionSheafification (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    Basic.singularCochains M (TopCat.of (⊤ : Opens X)) ⟶ singularSheafGlobalSections M X where
  f n := (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
    (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n)).app (op ⊤)
  comm' i j _ := by
    exact (congrArg (fun f => f.app (op (⊤ : Opens X)))
      (CategoryTheory.toSheafify_naturality (Opens.grothendieckTopology X)
        ((DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X).d i j))).symm

/-- The component is exactly the ordinary presheaf-to-sheaf unit on global sections. -/
@[simp]
theorem singularTopSectionSheafification_f (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    (singularTopSectionSheafification M X).f n =
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n)).app (op ⊤) := rfl

/-- The canonical map from cochains on the original space to global sections
of the sheafified singular complex. -/
def singularCochainsToSheafSections (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    Basic.singularCochains M X ⟶ singularSheafGlobalSections M X :=
  Functor.singularPullback M (Opens.inclusion' (⊤ : Opens X)) ≫
    singularTopSectionSheafification M X

@[simp]
theorem singularCochainsToSheafSections_f (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    (singularCochainsToSheafSections M X).f n =
      (Functor.singularPullback M (Opens.inclusion' (⊤ : Opens X))).f n ≫
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n)).app (op ⊤) := rfl

/-- Restricting the top-open representative is the actual restriction of the
original singular cochain to the smaller open set. -/
theorem singularTopRestriction_restrict (M : ModuleCat.{0} R) (X : TopCat.{0})
    (n : ℕ) (c : (Basic.singularCochains M X).X n) (V : Opens X) (i : V ⟶ ⊤) :
    (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n).map i.op
        ((Functor.singularPullback M (Opens.inclusion' (⊤ : Opens X))).f n c) =
      (Functor.singularPullback M (Opens.inclusion' V)).f n c := by
  have h : Functor.singularPullback M (Opens.inclusion' (⊤ : Opens X)) ≫
      Functor.singularPullback M ((Opens.toTopCat X).map i) =
        Functor.singularPullback M (Opens.inclusion' V) := by
    rw [← Functor.singularPullback_comp]
    rfl
  exact ConcreteCategory.congr_hom (congrArg (fun f => f.f n) h) c

/-- A singular cochain is locally zero when its actual restriction vanishes
on an open neighborhood of every point. -/
def IsLocallyZeroSingularCochain (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ)
    (c : (Basic.singularCochains M X).X n) : Prop :=
  ∀ x : X, ∃ V : Opens X, x ∈ V ∧
    (Functor.singularPullback M (Opens.inclusion' V)).f n c = 0

/-- The canonical map to global sheafified sections kills exactly the
locally zero singular cochains. No surjectivity assertion is used. -/
theorem singularCochainsToSheafSections_eq_zero_iff (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (n : ℕ) (c : (Basic.singularCochains M X).X n) :
    (singularCochainsToSheafSections M X).f n c = 0 ↔
      IsLocallyZeroSingularCochain M X n c := by
  change (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n)).app (op ⊤)
      ((Functor.singularPullback M (Opens.inclusion' (⊤ : Opens X))).f n c) = 0 ↔ _
  rw [sheafificationUnit_eq_zero_iff_locally_zero]
  constructor
  · intro h x
    obtain ⟨V, hxV, i, hi⟩ := h x (by trivial)
    exact ⟨V, hxV, (singularTopRestriction_restrict M X n c V i).symm.trans hi⟩
  · intro h x _
    obtain ⟨V, hxV, hV⟩ := h x
    exact ⟨V, hxV, homOfLE le_top,
      (singularTopRestriction_restrict M X n c V (homOfLE le_top)).trans hV⟩

/-- The actual linear submodule of locally zero singular cochains. -/
def locallyZeroCochainSubmodule (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    Submodule R ((Basic.singularCochains M X).X n) :=
  LinearMap.ker ((singularCochainsToSheafSections M X).f n).hom

@[simp]
theorem mem_locallyZeroCochainSubmodule (M : ModuleCat.{0} R) (X : TopCat.{0})
    (n : ℕ) (c : (Basic.singularCochains M X).X n) :
    c ∈ locallyZeroCochainSubmodule M X n ↔ IsLocallyZeroSingularCochain M X n c :=
  singularCochainsToSheafSections_eq_zero_iff M X n c

/-- The categorical kernel complex of locally zero singular cochains. -/
def locallyZeroSingularCochains (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  kernel (singularCochainsToSheafSections M X)

/-- The actual inclusion of locally zero cochains into all singular cochains. -/
def locallyZeroSingularInclusion (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    locallyZeroSingularCochains M X ⟶ Basic.singularCochains M X :=
  kernel.ι (singularCochainsToSheafSections M X)

/-- Its degreewise image is precisely the proved locally zero submodule. -/
theorem locallyZeroSingularInclusion_range (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    LinearMap.range ((locallyZeroSingularInclusion M X).f n).hom =
      locallyZeroCochainSubmodule M X n := by
  have h := (ShortComplex.kernelSequence_exact (singularCochainsToSheafSections M X)).map
    (HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.up ℕ) n)
  exact h.moduleCat_range_eq_ker

/-- Restriction to any family of small singular simplices is degreewise
surjective: an arbitrary function extends from the actual subset of simplices. -/
theorem smallSingularRestriction_f_surjective (M : ModuleCat.{0} R) (X : TopCat.{0})
    {J : Type} (U : J → Set X) (n : ℕ) :
    Function.Surjective ((DeRham.Comparison.SmallSingularCochains.smallSingularRestriction M X U).f n) := by
  classical
  intro c
  let j : (DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet) _⦋n⦌ → (TopCat.toSSet.obj X) _⦋n⦌ :=
    Subtype.val
  have hj : Function.Injective j := Subtype.val_injective
  let f := Function.extend j
    ((Coefficients.degreewiseFunctionIso (DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet) M n).hom c) (fun _ => 0)
  refine ⟨(Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M n).inv f, ?_⟩
  apply (Coefficients.degreewiseFunctionIso (DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet) M n).toLinearEquiv.injective
  change (Coefficients.degreewiseFunctionIso (DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet) M n).hom _ =
    (Coefficients.degreewiseFunctionIso (DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet) M n).hom c
  funext s
  change (Coefficients.degreewiseFunctionIso (DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet) M n).hom
    ((Functor.simplicialPullback M (DeRham.Comparison.SmallSingularSet.smallSingularInclusion X U)).f n
      ((Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M n).inv f)) s = _
  rw [Formulas.degreewiseFunctionIso_pullback, Iso.inv_hom_id_apply]
  exact hj.extend_apply _ _ s

/-- Restriction to an open member factors through the genuine small-cochain complex. -/
theorem smallSingularRestriction_open_restrict (M : ModuleCat.{0} R) (X : TopCat.{0})
    {J : Type} (U : J → Opens X) (i : J) :
    DeRham.Comparison.SmallSingularCochains.smallSingularRestriction M X (fun j => (U j : Set X)) ≫
      Functor.simplicialPullback M (NaturalSmallChains.coverMemberSingularMap X (fun j => (U j : Set X)) i) =
        Functor.singularPullback M (Opens.inclusion' (U i)) := by
  rw [DeRham.Comparison.SmallSingularCochains.smallSingularRestriction, ← Functor.simplicialPullback_comp,
    NaturalSmallChains.coverMemberSingularMap_inclusion]
  rfl

/-- Vanishing on small simplices is exactly vanishing after restriction to
every member of the actual open family. -/
theorem smallSingularRestriction_eq_zero_iff (M : ModuleCat.{0} R) (X : TopCat.{0})
    {J : Type} (U : J → Opens X) (n : ℕ) (c : (Basic.singularCochains M X).X n) :
    (DeRham.Comparison.SmallSingularCochains.smallSingularRestriction M X (fun j => (U j : Set X))).f n c = 0 ↔
      ∀ i, (Functor.singularPullback M (Opens.inclusion' (U i))).f n c = 0 := by
  constructor
  · intro hc i
    have h := ConcreteCategory.congr_hom
      (congrArg (fun f => f.f n) (smallSingularRestriction_open_restrict M X U i)) c
    change (Functor.simplicialPullback M
      (NaturalSmallChains.coverMemberSingularMap X (fun j => (U j : Set X)) i)).f n
      ((DeRham.Comparison.SmallSingularCochains.smallSingularRestriction M X (fun j => (U j : Set X))).f n c) = _ at h
    rw [hc, map_zero] at h
    exact h.symm
  · intro hc
    apply (Coefficients.degreewiseFunctionIso
      (DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X (fun j => (U j : Set X)) : SSet) M n).toLinearEquiv.injective
    change (Coefficients.degreewiseFunctionIso
        (DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X (fun j => (U j : Set X)) : SSet) M n).hom _ =
      (Coefficients.degreewiseFunctionIso
        (DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X (fun j => (U j : Set X)) : SSet) M n).hom 0
    funext s
    obtain ⟨i, hi⟩ := s.property
    obtain ⟨t, ht⟩ := NaturalSmallChains.singularSimplex_liftsToSubspace X (U i : Set X) n s.val hi
    change (TopCat.toSSet.map (Opens.inclusion' (U i))).app (op ⦋n⦌) t = s.val at ht
    have he := Formulas.degreewiseFunctionIso_pullback M
      (TopCat.toSSet.map (Opens.inclusion' (U i))) c t
    rw [ht] at he
    calc
      _ = (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M n).hom c s.val :=
        Formulas.degreewiseFunctionIso_pullback M
          (DeRham.Comparison.SmallSingularSet.smallSingularInclusion X (fun j => (U j : Set X))) c s
      _ = (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (TopCat.of (U i))) M n).hom
          ((Functor.singularPullback M (Opens.inclusion' (U i))).f n c) t := he.symm
      _ = 0 := by rw [hc i, map_zero]; rfl
      _ = _ := by rw [map_zero]; rfl

/-- A locally zero cochain vanishes on the small simplices of one actual open
cover, chosen with a neighborhood for each point. -/
theorem isLocallyZeroSingularCochain_iff_smallRestriction (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (n : ℕ) (c : (Basic.singularCochains M X).X n) :
    IsLocallyZeroSingularCochain M X n c ↔
      ∃ U : X → Opens X, (∀ x, x ∈ U x) ∧
        (DeRham.Comparison.SmallSingularCochains.smallSingularRestriction M X (fun x => (U x : Set X))).f n c = 0 := by
  classical
  constructor
  · intro hc
    choose U hmem hz using hc
    exact ⟨U, hmem, (smallSingularRestriction_eq_zero_iff M X U n c).2 hz⟩
  · rintro ⟨U, hmem, hz⟩ x
    exact ⟨U x, hmem x, (smallSingularRestriction_eq_zero_iff M X U n c).1 hz x⟩

/-- The inclusion of the actual kernel complex is injective in every degree. -/
theorem locallyZeroSingularInclusion_f_injective (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (n : ℕ) :
    Function.Injective ((locallyZeroSingularInclusion M X).f n) := by
  change Function.Injective ((kernel.ι (singularCochainsToSheafSections M X)).f n)
  exact (ModuleCat.mono_iff_injective _).1 inferInstance

/-- An element of the kernel complex gives a literally locally zero cochain. -/
theorem locallyZeroSingularInclusion_isLocallyZero (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (n : ℕ) (c : (locallyZeroSingularCochains M X).X n) :
    IsLocallyZeroSingularCochain M X n ((locallyZeroSingularInclusion M X).f n c) := by
  apply (mem_locallyZeroCochainSubmodule M X n _).1
  rw [← locallyZeroSingularInclusion_range]
  exact ⟨c, rfl⟩

/-- Every literally locally zero cochain lifts to the actual kernel complex. -/
theorem exists_locallyZeroSingularLift (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ)
    (c : (Basic.singularCochains M X).X n) (hc : IsLocallyZeroSingularCochain M X n c) :
    ∃ z : (locallyZeroSingularCochains M X).X n,
      (locallyZeroSingularInclusion M X).f n z = c := by
  have hmem := (mem_locallyZeroCochainSubmodule M X n c).2 hc
  rw [← locallyZeroSingularInclusion_range] at hmem
  exact hmem

/-- A locally zero positive-degree cocycle has a locally zero primitive.
The primitive vanishes on the same chosen open cover's small simplices. -/
theorem exists_locallyZeroSingularPrimitive (F : Type) [Field F] [CharZero F]
    (X : TopCat.{0}) (n : ℕ) (c : (Basic.singularCochains (ModuleCat.of F F) X).X (n + 1))
    (hc : (Basic.singularCochains (ModuleCat.of F F) X).d (n + 1) (n + 2) c = 0)
    (hlocal : IsLocallyZeroSingularCochain (ModuleCat.of F F) X (n + 1) c) :
    ∃ b : (Basic.singularCochains (ModuleCat.of F F) X).X n,
      (Basic.singularCochains (ModuleCat.of F F) X).d n (n + 1) b = c ∧
        IsLocallyZeroSingularCochain (ModuleCat.of F F) X n b := by
  obtain ⟨U, hU, hsmall⟩ :=
    (isLocallyZeroSingularCochain_iff_smallRestriction (ModuleCat.of F F) X (n + 1) c).1 hlocal
  have : QuasiIso (DeRham.Comparison.SmallSingularCochains.smallSingularRestriction (ModuleCat.of F F) X (fun x => (U x : Set X))) :=
    SmallCochainComparison.smallSingularRestriction_quasiIso X (fun x => (U x : Set X)) F
      (fun x => (U x).isOpen) (fun x => ⟨x, hU x⟩)
  obtain ⟨b, hb, hbsmall⟩ := SurjectiveQuasiIso.exists_primitive_in_kernel_of_surjective_quasiIso
    (DeRham.Comparison.SmallSingularCochains.smallSingularRestriction (ModuleCat.of F F) X (fun x => (U x : Set X)))
    (smallSingularRestriction_f_surjective (ModuleCat.of F F) X (fun x => (U x : Set X)))
    n c hc hsmall
  exact ⟨b, hb,
    (isLocallyZeroSingularCochain_iff_smallRestriction (ModuleCat.of F F) X n b).2
      ⟨U, hU, hbsmall⟩⟩

/-- A locally zero closed singular zero-cochain vanishes. -/
theorem locallyZeroSingularCocycle_zero (F : Type) [Field F] [CharZero F]
    (X : TopCat.{0}) (c : (Basic.singularCochains (ModuleCat.of F F) X).X 0)
    (hc : (Basic.singularCochains (ModuleCat.of F F) X).d 0 1 c = 0)
    (hlocal : IsLocallyZeroSingularCochain (ModuleCat.of F F) X 0 c) : c = 0 := by
  obtain ⟨U, hU, hsmall⟩ :=
    (isLocallyZeroSingularCochain_iff_smallRestriction (ModuleCat.of F F) X 0 c).1 hlocal
  have : QuasiIso (DeRham.Comparison.SmallSingularCochains.smallSingularRestriction (ModuleCat.of F F) X (fun x => (U x : Set X))) :=
    SmallCochainComparison.smallSingularRestriction_quasiIso X (fun x => (U x : Set X)) F
      (fun x => (U x).isOpen) (fun x => ⟨x, hU x⟩)
  exact SurjectiveQuasiIso.cochain_eq_zero_in_kernel_of_surjective_quasiIso
    (DeRham.Comparison.SmallSingularCochains.smallSingularRestriction (ModuleCat.of F F) X (fun x => (U x : Set X)))
    (smallSingularRestriction_f_surjective (ModuleCat.of F F) X (fun x => (U x : Set X)))
    c hc hsmall

/-- The genuine locally zero singular subcomplex is acyclic over any
characteristic-zero field. This requires no local or global hypothesis on X. -/
theorem locallyZeroSingularCochains_acyclic (F : Type) [Field F] [CharZero F]
    (X : TopCat.{0}) : (locallyZeroSingularCochains (ModuleCat.of F F) X).Acyclic := by
  let K := locallyZeroSingularCochains (ModuleCat.of F F) X
  let i := locallyZeroSingularInclusion (ModuleCat.of F F) X
  intro k
  cases k with
  | zero =>
    apply (K.exactAt_iff' 0 0 1 (by simp) (by simp)).2
    apply (ShortComplex.moduleCat_exact_iff _).2
    intro z hz
    have hc : (Basic.singularCochains (ModuleCat.of F F) X).d 0 1 (i.f 0 z) = 0 := by
      simpa only [map_zero] using LocalPrimitives.cochainMap_primitive i 0 z 0 hz
    have hz0 := locallyZeroSingularCocycle_zero F X (i.f 0 z) hc
      (locallyZeroSingularInclusion_isLocallyZero (ModuleCat.of F F) X 0 z)
    have hzero : z = 0 := by
      apply locallyZeroSingularInclusion_f_injective (ModuleCat.of F F) X 0
      change i.f 0 z = i.f 0 0
      rw [hz0, map_zero]
    refine ⟨0, ?_⟩
    change K.d 0 0 0 = z
    exact (K.d 0 0).hom.map_zero.trans hzero.symm
  | succ n =>
    apply (K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)).2
    apply (ShortComplex.moduleCat_exact_iff _).2
    intro z hz
    have hc : (Basic.singularCochains (ModuleCat.of F F) X).d (n + 1) (n + 2)
        (i.f (n + 1) z) = 0 := by
      simpa only [map_zero] using LocalPrimitives.cochainMap_primitive i (n + 1) z 0 hz
    obtain ⟨b, hb, hblocal⟩ := exists_locallyZeroSingularPrimitive F X n (i.f (n + 1) z) hc
      (locallyZeroSingularInclusion_isLocallyZero (ModuleCat.of F F) X (n + 1) z)
    obtain ⟨w, hw⟩ := exists_locallyZeroSingularLift (ModuleCat.of F F) X n b hblocal
    refine ⟨w, ?_⟩
    apply locallyZeroSingularInclusion_f_injective (ModuleCat.of F F) X (n + 1)
    change i.f (n + 1) (K.d n (n + 1) w) = i.f (n + 1) z
    have hcomm := LocalPrimitives.cochainMap_primitive i n w (K.d n (n + 1) w) rfl
    exact hcomm.symm.trans ((congrArg ((Basic.singularCochains (ModuleCat.of F F) X).d n (n + 1)) hw).trans hb)

/-- Every cohomology object of the genuine locally zero complex is zero. -/
theorem isZero_locallyZeroSingularCohomology (F : Type) [Field F] [CharZero F]
    (X : TopCat.{0}) (n : ℕ) :
    IsZero ((locallyZeroSingularCochains (ModuleCat.of F F) X).homology n) :=
  (locallyZeroSingularCochains_acyclic F X n).isZero_homology

end

end OAI.AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains
