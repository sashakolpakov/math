import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingRepresentative
import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.Winding
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.Cech
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.CechComparison

/-! # Subspace Cech D -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SubspaceCechD

noncomputable section

section

/-!
# ChernClass: a relative cocycle for the winding of a local equation

Extend winding values by zero from the actual subspace simplices. The
differential of this explicit ambient cochain has zero restriction, so it
lifts uniquely to the relative complex. The connecting-map formula identifies
its class with the already constructed supported winding class.
-/

open _root_.CategoryTheory
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : TopCat.{0}) (A : Set X)

/-- The actual inclusion of singular simplices of a subspace. -/
def subspaceSimplexMap (n : ℕ) :
    (TopCat.toSSet.obj (TopCat.of A)) _⦋n⦌ → (TopCat.toSSet.obj X) _⦋n⦌ :=
  (TopCat.toSSet.map (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A)).app _

theorem subspaceSimplexMap_injective (n : ℕ) :
    Function.Injective (subspaceSimplexMap X A n) := by
  exact (CategoryTheory.mono_iff_injective
    ((TopCat.toSSet.map (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A)).app _)).mp inferInstance

/-- Extend a subspace cochain by zero on simplices outside the inclusion's image. -/
def zeroExtendCochain (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of A)).X n) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n :=
  (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) n).inv
    (Function.extend (subspaceSimplexMap X A n)
      ((AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (TopCat.of A)) (ModuleCat.of ℚ ℚ) n).hom c)
      (fun _ => 0))

theorem zeroExtendCochain_value (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of A)).X n)
    (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) n).hom
      (zeroExtendCochain X A n c) s =
      Function.extend (subspaceSimplexMap X A n)
        ((AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (TopCat.of A)) (ModuleCat.of ℚ ℚ) n).hom c)
        (fun _ => 0) s := by
  unfold zeroExtendCochain
  rw [Iso.inv_hom_id_apply]

/-- The explicit extension really restricts to the given cochain. -/
theorem zeroExtendCochain_restrict (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of A)).X n) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f n
      (zeroExtendCochain X A n c) = c := by
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (TopCat.of A))
    (ModuleCat.of ℚ ℚ) n).toLinearEquiv.injective
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (TopCat.of A))
    (ModuleCat.of ℚ ℚ) n).hom _ = _
  ext s
  have h := AlgebraicTopology.Cohomology.Singular.Formulas.degreewiseFunctionIso_pullback (ModuleCat.of ℚ ℚ)
    (TopCat.toSSet.map (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A)) (zeroExtendCochain X A n c) s
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (TopCat.of A)) (ModuleCat.of ℚ ℚ) n).hom
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f n (zeroExtendCochain X A n c)) s =
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) n).hom
      (zeroExtendCochain X A n c) (subspaceSimplexMap X A n s) at h
  rw [h, zeroExtendCochain_value]
  exact (subspaceSimplexMap_injective X A n).extend_apply _ _ s

/-- Relative inclusion is injective in each degree. -/
theorem relativeCochainInclusion_injective (n : ℕ) :
    Function.Injective ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f n) := by
  let := (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainSequence_degreewiseShortExact (ModuleCat.of ℚ ℚ) X A n).mono_f
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

/-- A cochain with zero restriction has a unique lift to the actual relative complex. -/
theorem existsUnique_relativeLift (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n)
    (hc : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f n c = 0) :
    ∃! a : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X n,
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f n a = c := by
  have hmem : c ∈ LinearMap.range ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f n).hom := by
    rw [AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_range]
    exact hc
  obtain ⟨a, ha⟩ := hmem
  exact ⟨a, ha, fun b hb => relativeCochainInclusion_injective X A n (hb.trans ha.symm)⟩

/-- A chosen notation for the unique relative lift; it has no choice ambiguity. -/
def relativeLift (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n)
    (hc : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f n c = 0) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X n :=
  (existsUnique_relativeLift X A n c hc).exists.choose

theorem relativeLift_inclusion (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n)
    (hc : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f n c = 0) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f n (relativeLift X A n c hc) = c :=
  (existsUnique_relativeLift X A n c hc).exists.choose_spec

/-- Lifting a closed cochain to the relative kernel preserves closedness. -/
theorem relativeLift_closed (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n)
    (hc : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f n c = 0)
    (hd : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d n (n + 1) c = 0) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).d n (n + 1)
      (relativeLift X A n c hc) = 0 := by
  apply relativeCochainInclusion_injective X A (n + 1)
  have h := ConcreteCategory.congr_hom
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).comm n (n + 1))
    (relativeLift X A n c hc)
  change (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d n (n + 1)
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f n (relativeLift X A n c hc)) =
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f (n + 1)
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).d n (n + 1)
        (relativeLift X A n c hc)) at h
  rw [relativeLift_inclusion, hd] at h
  exact h.symm.trans (map_zero _).symm

/-- The differential of an extended cocycle restricts to zero. -/
theorem zeroExtendCocycle_d_restrict (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) (TopCat.of A) n) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f (n + 1)
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d n (n + 1)
        (zeroExtendCochain X A n c.val)) = 0 := by
  have h := ConcreteCategory.congr_hom
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).comm n (n + 1))
    (zeroExtendCochain X A n c.val)
  change (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of A)).d n (n + 1)
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f n
        (zeroExtendCochain X A n c.val)) =
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f (n + 1)
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d n (n + 1)
        (zeroExtendCochain X A n c.val)) at h
  rw [zeroExtendCochain_restrict] at h
  exact h.symm.trans ((AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff _ n c.val).mp c.property)

/-- The actual relative connecting cocycle obtained by zero extension. -/
def zeroExtensionConnectingCocycle (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) (TopCat.of A) n) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) (n + 1) :=
  ⟨relativeLift X A (n + 1)
    ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d n (n + 1) (zeroExtendCochain X A n c.val))
    (zeroExtendCocycle_d_restrict X A n c), by
      rw [AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff]
      apply relativeLift_closed
      exact ConcreteCategory.congr_hom
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d_comp_d n (n + 1) (n + 1 + 1))
        (zeroExtendCochain X A n c.val)⟩

theorem zeroExtensionConnectingCocycle_inclusion (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) (TopCat.of A) n) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f (n + 1)
      (zeroExtensionConnectingCocycle X A n c).val =
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d n (n + 1) (zeroExtendCochain X A n c.val) :=
  relativeLift_inclusion X A (n + 1) _ (zeroExtendCocycle_d_restrict X A n c)

/-- The explicit cocycle computes the constructed long-exact-sequence map. -/
theorem zeroExtensionConnectingCocycle_class (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) (TopCat.of A) n) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) (n + 1)
      (zeroExtensionConnectingCocycle X A n c) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting (ModuleCat.of ℚ ℚ) X A n
      (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) (TopCat.of A) n c) :=
  (ConnectingRepresentative.relativeConnecting_class_of_lift X A n c (zeroExtendCochain X A n c.val)
    (zeroExtensionConnectingCocycle X A n c) (zeroExtendCochain_restrict X A n c.val)
    (zeroExtensionConnectingCocycle_inclusion X A n c)).symm

/-- A genuine relative degree-two cocycle for the winding of a local equation. -/
def relativeWindingCocycle (g : C(A, ℂ)) (hg : ∀ x, g x ≠ 0) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) 2 :=
  zeroExtensionConnectingCocycle X A 1 (WindingSingular.singularWindingCocycle (TopCat.of A) g hg)

/-- Its class is the supported winding class already used for rational sections. -/
theorem relativeWindingCocycle_class (g : C(A, ℂ)) (hg : ∀ x, g x ≠ 0) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) 2
      (relativeWindingCocycle X A g hg) = Supported.Winding.supportedWindingClass X A g hg :=
  zeroExtensionConnectingCocycle_class X A 1 (WindingSingular.singularWindingCocycle (TopCat.of A) g hg)

end

section

/-!
# ChernClass: restriction of Cech cochains to the removed subspace

All coefficient objects are the actual singular cochains on `U ∩ A`.
Restriction is natural, commutes with both differentials, and has exactly
the relative cochains as its kernel on every finite intersection.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech

variable (X : TopCat.{0}) (A : Set X)

/-- Intersect an analytic open with the actual subspace, with the subspace topology. -/
def intersectionSubspaceFunctor : Opens X ⥤ TopCat.{0} where
  obj U := TopCat.of (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace A U)
  map f := TopCat.ofHom
    ⟨fun p => ⟨⟨p.val.val, f.le p.val.property⟩, p.property⟩,
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Singular cochains on the intersections with the subspace. -/
def subspaceSingularCochainPresheaf :
    X.Presheaf (CochainComplex (ModuleCat.{0} ℚ) ℕ) :=
  (intersectionSubspaceFunctor X A).op ⋙ AlgebraicTopology.Cohomology.Singular.Functor.singularCochainsFunctor (ModuleCat.of ℚ ℚ)

def subspaceSingularDegreePresheaf (n : ℕ) : X.Presheaf (ModuleCat.{0} ℚ) :=
  subspaceSingularCochainPresheaf X A ⋙
    HomologicalComplex.eval (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) n

/-- The ordinary differentials on those actual subspaces. -/
def subspaceSingularPresheafComplex :
    CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{0} ℚ) ℕ where
  X := subspaceSingularDegreePresheaf X A
  d i j := {
    app := fun U => ((subspaceSingularCochainPresheaf X A).obj U).d i j
    naturality := fun _ _ f => ((subspaceSingularCochainPresheaf X A).map f).comm i j }
  shape i j h := by
    apply NatTrans.ext
    funext U
    exact ((subspaceSingularCochainPresheaf X A).obj U).shape i j h
  d_comp_d' i j k _ _ := by
    apply NatTrans.ext
    funext U
    exact ((subspaceSingularCochainPresheaf X A).obj U).d_comp_d i j k

/-- Restriction to `A` is natural on actual open subsets. -/
def subspaceSingularPresheafRestriction :
    AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainPresheaf (ModuleCat.of ℚ ℚ) X ⟶ subspaceSingularCochainPresheaf X A where
  app U := AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) (TopCat.of U.unop)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace A U.unop)
  naturality U V f := by
    change AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) ((Opens.toTopCat X).map f.unop) ≫
        AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.unop)
          (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace A V.unop)) =
      AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of U.unop)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace A U.unop)) ≫
        AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) ((intersectionSubspaceFunctor X A).map f.unop)
    rw [← AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp, ← AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp]
    rfl

/-- The cochain restriction as a morphism of the actual presheaf complexes. -/
def subspacePresheafRestriction :
    AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X ⟶ subspaceSingularPresheafComplex X A where
  f n := Functor.whiskerRight (subspaceSingularPresheafRestriction X A)
    (HomologicalComplex.eval (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) n)
  comm' i j _ := by
    apply NatTrans.ext
    funext U
    exact ((subspaceSingularPresheafRestriction X A).app U).comm i j

variable {I : Type} (U : I → Opens X)

theorem subspaceCechVertical_apply (p q : ℕ)
    (c : Rational.Cech.RationalCech.CechCochain (subspaceSingularDegreePresheaf X A q) U p) (a : Fin (p + 1) → I) :
    Rational.Cech.RationalCech.cechCoefficientMap U ((subspaceSingularPresheafComplex X A).d q (q + 1)) p c a =
      (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ)
        (TopCat.of (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace A (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)))).d q (q + 1) (c a) := rfl

/-- Restriction of singular Cech cochains to the removed subspaces. -/
abbrev subspaceCechRestriction (p q : ℕ) :=
  Rational.Cech.RationalCech.cechCoefficientMap U ((subspacePresheafRestriction X A).f q) p

/-- A cochain on the subspace has an explicit extension on each open intersection. -/
def subspaceCechExtension (p q : ℕ) (c : Rational.Cech.RationalCech.CechCochain (subspaceSingularDegreePresheaf X A q) U p) :
    Rational.Cech.RationalCech.CechCochain (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℚ ℚ) X q) U p :=
  fun a => zeroExtendCochain (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace A (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) q (c a)

theorem subspaceCechExtension_restrict (p q : ℕ)
    (c : Rational.Cech.RationalCech.CechCochain (subspaceSingularDegreePresheaf X A q) U p) :
    subspaceCechRestriction X A U p q (subspaceCechExtension X A U p q c) = c := by
  funext a
  exact zeroExtendCochain_restrict (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace A (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) q (c a)

/-- Inclusion of actual relative Cech cochains into absolute Cech cochains. -/
abbrev relativeCechInclusion (p q : ℕ) :=
  Rational.Cech.RationalCech.cechCoefficientMap U ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativePresheafInclusion (ModuleCat.of ℚ ℚ) X A).f q) p

theorem relativeCechInclusion_injective (p q : ℕ) :
    Function.Injective (relativeCechInclusion X A U p q) := by
  intro c d h
  funext a
  exact relativeCochainInclusion_injective (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace A (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) q (congrFun h a)

/-- A family with zero subspace restriction lifts to the original relative cochain kernels. -/
def relativeCechLift (p q : ℕ)
    (c : Rational.Cech.RationalCech.CechCochain (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℚ ℚ) X q) U p)
    (hc : subspaceCechRestriction X A U p q c = 0) :
    Rational.Cech.RationalCech.CechCochain (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainDegreePresheaf (ModuleCat.of ℚ ℚ) X A q) U p :=
  fun a => relativeLift (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace A (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) q (c a) (congrFun hc a)

theorem relativeCechLift_inclusion (p q : ℕ)
    (c : Rational.Cech.RationalCech.CechCochain (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℚ ℚ) X q) U p)
    (hc : subspaceCechRestriction X A U p q c = 0) :
    relativeCechInclusion X A U p q (relativeCechLift X A U p q c hc) = c := by
  funext a
  exact relativeLift_inclusion (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace A (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) q (c a) (congrFun hc a)

end RationalCech

end

section

/-!
# ChernClass: the genuine induced cover on a subspace

Finite intersections in the induced cover have their actual subspace
topologies. Swapping the two subtype conditions identifies them with the
coefficient domains of the subspace Cech complex, naturally in every tuple.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech

variable {I : Type} (X : TopCat.{0}) (A : Set X) (U : I → Opens X)

/-- Pull back the actual open family along the subspace inclusion. -/
def inducedSubspaceCover (i : I) : Opens (TopCat.of A) :=
  Opens.comap (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) (U i)

theorem inducedSubspaceCover_covers (hU : ∀ x : X, ∃ i, x ∈ U i) :
    ∀ x : TopCat.of A, ∃ i, x ∈ inducedSubspaceCover X A U i :=
  fun x => hU x.val

theorem mem_inducedSubspaceIntersection {n : ℕ} (a : Fin (n + 1) → I) (x : A) :
    x ∈ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (inducedSubspaceCover X A U) a ↔ x.val ∈ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a := by
  rw [AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection, AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection]
  rfl

/-- The two nested subspaces are the same geometric points with the same topology. -/
def subspaceIntersectionHomeomorph {n : ℕ} (a : Fin (n + 1) → I) :
    AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (inducedSubspaceCover X A U) a ≃ₜ AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace A (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) where
  toFun p := ⟨⟨p.val.val, (mem_inducedSubspaceIntersection X A U a p.val).mp p.property⟩, p.val.property⟩
  invFun p := ⟨⟨p.val.val, p.property⟩,
    (mem_inducedSubspaceIntersection X A U a ⟨p.val.val, p.property⟩).mpr p.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

/-- The actual continuous map from an induced-cover intersection to its coefficient domain. -/
def subspaceIntersectionIso {n : ℕ} (a : Fin (n + 1) → I) :
    TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (inducedSubspaceCover X A U) a) ≅
      TopCat.of (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace A (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) :=
  TopCat.isoOfHomeo (subspaceIntersectionHomeomorph X A U a)

/-- The swap commutes with every actual finite-intersection restriction. -/
theorem subspaceIntersectionIso_naturality {n m : ℕ}
    (a : Fin (m + 1) → I) (r : Fin (n + 1) → Fin (m + 1)) :
    (subspaceIntersectionIso X A U a).hom ≫
      (intersectionSubspaceFunctor X A).map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a r)) =
    (Opens.toTopCat (TopCat.of A)).map
      (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp (inducedSubspaceCover X A U) a r)) ≫
        (subspaceIntersectionIso X A U (a ∘ r)).hom := rfl

/-- Pullback along the actual homeomorphism identifies the actual cochain complexes. -/
def subspaceIntersectionCochainIso {n : ℕ} (a : Fin (n + 1) → I) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace A (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))) ≅
      AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ)
        (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (inducedSubspaceCover X A U) a)) :=
  (AlgebraicTopology.Cohomology.Singular.Functor.singularCochainsFunctor (ModuleCat.of ℚ ℚ)).mapIso (subspaceIntersectionIso X A U a).op

/-- The cochain identification commutes with the actual pullback restrictions. -/
theorem subspaceIntersectionCochainIso_naturality {n m : ℕ}
    (a : Fin (m + 1) → I) (r : Fin (n + 1) → Fin (m + 1)) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ)
        ((intersectionSubspaceFunctor X A).map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a r))) ≫
      (subspaceIntersectionCochainIso X A U a).hom =
    (subspaceIntersectionCochainIso X A U (a ∘ r)).hom ≫
      AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) ((Opens.toTopCat (TopCat.of A)).map
        (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp (inducedSubspaceCover X A U) a r))) := by
  change AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) _ ≫
      AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (subspaceIntersectionIso X A U a).hom =
    AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (subspaceIntersectionIso X A U (a ∘ r)).hom ≫
      AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) _
  rw [← AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp, ← AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp, subspaceIntersectionIso_naturality]

end RationalCech

end

/-!
# ChernClass: subspace Cech cochains and the native induced-cover complex

The actual homeomorphisms of finite intersections induce an isomorphism of
the Cech double complexes. No replacement of the singular cochain theory or
of its restriction maps occurs in this transport.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech

variable {I : Type} (X : TopCat.{0}) (A : Set X) (U : I → Opens X)

local notation "K" => OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.Cech.RationalCech.cechDoubleComplex U (OAI.AlgebraicGeometry.DivisorClass.Chern.SubspaceCechD.RationalCech.subspaceSingularPresheafComplex X A)
local notation "N" => OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechDoubleComplex (TopCat.of A) (OAI.AlgebraicGeometry.DivisorClass.Chern.SubspaceCechD.RationalCech.inducedSubspaceCover X A U) (ModuleCat.of ℚ ℚ)

/-- The genuine pullback of every coefficient cochain along its intersection homeomorphism. -/
def subspaceCechColumnMap (p : ℕ) : (K).X p ⟶ (N).X p where
  f q := ModuleCat.ofHom {
    toFun := fun c a => (subspaceIntersectionCochainIso X A U a).hom.f q (c a)
    map_add' := by intro c d; funext a; exact map_add _ _ _
    map_smul' := by intro r c; funext a; exact map_smul _ _ _ }
  comm' q r _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext a
    exact ConcreteCategory.congr_hom ((subspaceIntersectionCochainIso X A U a).hom.comm q r) (c a)

/-- Pullback along the inverse homeomorphisms. -/
def subspaceCechColumnInverse (p : ℕ) : (N).X p ⟶ (K).X p where
  f q := ModuleCat.ofHom {
    toFun := fun c a => (subspaceIntersectionCochainIso X A U a).inv.f q (c a)
    map_add' := by intro c d; funext a; exact map_add _ _ _
    map_smul' := by intro r c; funext a; exact map_smul _ _ _ }
  comm' q r _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext a
    exact ConcreteCategory.congr_hom ((subspaceIntersectionCochainIso X A U a).inv.comm q r) (c a)

/-- The actual section-family cochain complexes are isomorphic. -/
def subspaceCechColumnIso (p : ℕ) : (K).X p ≅ (N).X p where
  hom := subspaceCechColumnMap X A U p
  inv := subspaceCechColumnInverse X A U p
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext a
    exact ConcreteCategory.congr_hom
      (congrArg (fun f => f.f q) (subspaceIntersectionCochainIso X A U a).hom_inv_id) (c a)
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext a
    exact ConcreteCategory.congr_hom
      (congrArg (fun f => f.f q) (subspaceIntersectionCochainIso X A U a).inv_hom_id) (c a)

/-- Compatibility with every Cech tuple map follows from the actual inclusion square. -/
theorem subspaceCechColumnMap_precomp {n m : ℕ}
    (r : Fin (n + 1) → Fin (m + 1)) (q : ℕ)
    (c : Rational.Cech.RationalCech.CechCochain (subspaceSingularDegreePresheaf X A q) U n) :
    (subspaceCechColumnMap X A U m).f q (Rational.Cech.RationalCech.cechPrecomp (subspaceSingularDegreePresheaf X A q) U r c) =
    Rational.Cech.RationalCech.cechPrecomp (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℚ ℚ) (TopCat.of A) q)
      (inducedSubspaceCover X A U) r ((subspaceCechColumnMap X A U n).f q c) := by
  funext a
  exact ConcreteCategory.congr_hom
    (congrArg (fun f => f.f q) (subspaceIntersectionCochainIso_naturality X A U a r)) (c (a ∘ r))

/-- The horizontal Cech differentials commute with the actual intersection transport. -/
theorem subspaceCechColumnMap_horizontal (p q : ℕ) :
    ((K).d p (p + 1)).f q ≫ (subspaceCechColumnMap X A U (p + 1)).f q =
      (subspaceCechColumnMap X A U p).f q ≫ ((N).d p (p + 1)).f q := by
  rw [Rational.Cech.RationalCech.cechDoubleComplex_d_f, Rational.CechComparison.RationalCech.singularCechDoubleComplex_d_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  funext a
  change (subspaceIntersectionCochainIso X A U a).hom.f q
      (Rational.Cech.RationalCech.cechDelta (subspaceSingularDegreePresheaf X A q) U p c a) =
    Rational.Cech.RationalCech.cechDelta (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℚ ℚ) (TopCat.of A) q)
      (inducedSubspaceCover X A U) p ((subspaceCechColumnMap X A U p).f q c) a
  rw [Rational.Cech.RationalCech.cechDelta_apply, Rational.Cech.RationalCech.cechDelta_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_zsmul]
  apply congrArg (fun z => ((-1 : ℤ) ^ j.val) • z)
  exact congrFun (subspaceCechColumnMap_precomp X A U j.succAbove q c) a

/-- The constructed coefficient homeomorphisms identify the full native double complexes. -/
def subspaceCechDoubleIso : K ≅ N :=
  HomologicalComplex.Hom.isoOfComponents (subspaceCechColumnIso X A U) (by
    intro p r hpr
    obtain rfl : p + 1 = r := hpr
    apply HomologicalComplex.Hom.ext
    funext q
    exact (subspaceCechColumnMap_horizontal X A U p q).symm)

/-- The isomorphism on the actual signed total complexes. -/
def subspaceCechTotalIso :
    Rational.Cech.RationalCech.cechTotalComplex U (subspaceSingularPresheafComplex X A) ≅
      Rational.CechComparison.RationalCech.singularCechTotal (TopCat.of A) (inducedSubspaceCover X A U) (ModuleCat.of ℚ ℚ) :=
  (HomologicalComplex₂.totalFunctor (ModuleCat.{0} ℚ)
    (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)).mapIso (subspaceCechDoubleIso X A U)

end RationalCech

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SubspaceCechD
