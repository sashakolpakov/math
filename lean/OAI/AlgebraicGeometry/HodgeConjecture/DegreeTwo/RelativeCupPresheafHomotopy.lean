import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupHomotopy
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupSheaf

/-! # Relative Cup Presheaf Homotopy -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupPresheafHomotopy.Constructions

noncomputable section

section

/-! Relative cup primitives retain every open-set restriction and support condition. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (C : Set X)

theorem relativeCochainMap_cast {Y : TopCat.{0}} {D : Set Y}
    (f : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) Y D) {i j : ℕ} (h : i=j)
    (b : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).X i) :
    f.f j (CycleClass.Geometric.RelativeCup.Cycles.relativeCochainCast (ModuleCat.of ℚ ℚ) X C h b) =
      CycleClass.Geometric.RelativeCup.Cycles.relativeCochainCast (ModuleCat.of ℚ ℚ) Y D h (f.f i b) := by
  subst j
  rfl

variable (v : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).X 1)

theorem relativeOneCupSuccessorMap_naturality {Y : TopCat.{0}} (f : Y ⟶ X)
    (D : Set Y) (hf : Set.MapsTo f D C) (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) f).f (n+1) ≫
        RelativeCupHomotopy.Constructions.relativeOneCupSuccessorMap Y D
          ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f hf).f 1 v) n =
      RelativeCupHomotopy.Constructions.relativeOneCupSuccessorMap X C v n ≫
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f hf).f (2+n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  change CycleClass.Geometric.RelativeCup.Cycles.relativeCochainCast (ModuleCat.of ℚ ℚ) Y D _
      (CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup Y D 1 (n+1)
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f hf).f 1 v)
        ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) f).f (n+1) b)) =
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f hf).f (2+n)
      (CycleClass.Geometric.RelativeCup.Cycles.relativeCochainCast (ModuleCat.of ℚ ℚ) X C _ (CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X C 1 (n+1) v b))
  rw [relativeCochainMap_cast]
  apply congrArg (CycleClass.Geometric.RelativeCup.Cycles.relativeCochainCast (ModuleCat.of ℚ ℚ) Y D _)
  exact (CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCupWith_pullback Y D
    (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
    (LinearMap.mul ℚ ℚ) f hf v b).symm

theorem relativeOneCupZeroMap_naturality {Y : TopCat.{0}} (f : Y ⟶ X)
    (D : Set Y) (hf : Set.MapsTo f D C) :
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) f).f 0 ≫
        RelativeCupHomotopy.Constructions.relativeOneCupZeroMap Y D
          ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f hf).f 1 v) =
      RelativeCupHomotopy.Constructions.relativeOneCupZeroMap X C v ≫
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f hf).f 1 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  exact (CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCupWith_pullback Y D
    (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
    (LinearMap.mul ℚ ℚ) f hf v b).symm

def relativeOneCochainOpenRestriction (U : Opens X) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C U)).X 1 :=
  (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) (Opens.inclusion' U) (fun _ hx => hx)).f 1 v

theorem relativeOneCochainOpenRestriction_naturality {U W : Opens X} (i : U ⟶ W) :
    ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheaf (ModuleCat.of ℚ ℚ) X C).map i.op).f 1
        (relativeOneCochainOpenRestriction X C v W) =
      relativeOneCochainOpenRestriction X C v U := by
  have h := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp (ModuleCat.of ℚ ℚ)
    ((Opens.toTopCat X).map i) (Opens.inclusion' W)
    (A := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C U) (B := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C W) (C := C)
    (fun _ hx => hx) (fun _ hx => hx)
  exact ConcreteCategory.congr_hom (congrArg (fun f => f.f 1) h) v

def relativeOneCupSuccessorPresheafMap (n : ℕ) :
    (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X (n+1) ⟶
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativePresheafComplex (ModuleCat.of ℚ ℚ) X C).X (2+n) where
  app U := RelativeCupHomotopy.Constructions.relativeOneCupSuccessorMap (TopCat.of U.unop) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C U.unop)
    (relativeOneCochainOpenRestriction X C v U.unop) n
  naturality U W i := by
    have h := relativeOneCupSuccessorMap_naturality (TopCat.of U.unop)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C U.unop) (relativeOneCochainOpenRestriction X C v U.unop)
      ((Opens.toTopCat X).map i.unop) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C W.unop) (fun _ hx => hx) n
    have hc := congrArg (fun w =>
      (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) ((Opens.toTopCat X).map i.unop)).f (n+1) ≫
        RelativeCupHomotopy.Constructions.relativeOneCupSuccessorMap (TopCat.of W.unop) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C W.unop) w n)
      (relativeOneCochainOpenRestriction_naturality X C v i.unop)
    exact hc.symm.trans h

def relativeOneCupZeroPresheafMap :
    (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 0 ⟶
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativePresheafComplex (ModuleCat.of ℚ ℚ) X C).X 1 where
  app U := RelativeCupHomotopy.Constructions.relativeOneCupZeroMap (TopCat.of U.unop) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C U.unop)
    (relativeOneCochainOpenRestriction X C v U.unop)
  naturality U W i := by
    have h := relativeOneCupZeroMap_naturality (TopCat.of U.unop)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C U.unop) (relativeOneCochainOpenRestriction X C v U.unop)
      ((Opens.toTopCat X).map i.unop) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C W.unop) (fun _ hx => hx)
    have hc := congrArg (fun w =>
      (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) ((Opens.toTopCat X).map i.unop)).f 0 ≫
        RelativeCupHomotopy.Constructions.relativeOneCupZeroMap (TopCat.of W.unop) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C W.unop) w)
      (relativeOneCochainOpenRestriction_naturality X C v i.unop)
    exact hc.symm.trans h

end

/-! The global primitive restricts to coherent primitive identities of presheaves. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (C : Set X)
variable (v : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).X 1)
variable (a b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) 2)
variable (hv : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).d 1 2 v = a.val-b.val)

include hv in
theorem relativeOneCochainOpenRestriction_d (U : Opens X) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C U)).d 1 2
        (relativeOneCochainOpenRestriction X C v U) =
      (RelativeCupPresheaf.Constructions.relativeTwoCocycleOpenRestriction X C a U).val -
        (RelativeCupPresheaf.Constructions.relativeTwoCocycleOpenRestriction X C b U).val := by
  let f := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) (Opens.inclusion' U)
    (A := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C U) (B := C) (fun _ hx => hx)
  have h := ConcreteCategory.congr_hom (f.comm 1 2) v
  simp only [ConcreteCategory.comp_apply, hv, map_sub] at h
  exact h

include hv in
theorem relativeTwoCupPresheafPrimitive_zero :
    (RelativeCupPresheaf.Constructions.relativeTwoCupPresheafComplexMap X C a).f 0 - (RelativeCupPresheaf.Constructions.relativeTwoCupPresheafComplexMap X C b).f 0 =
      (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).d 0 1 ≫
        relativeOneCupSuccessorPresheafMap X C v 0 +
      relativeOneCupZeroPresheafMap X C v ≫
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativePresheafComplex (ModuleCat.of ℚ ℚ) X C).d 1 2 := by
  apply NatTrans.ext
  funext U
  exact RelativeCupHomotopy.Constructions.relativeTwoCupPrimitive_zero (TopCat.of U.unop) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C U.unop)
    (relativeOneCochainOpenRestriction X C v U.unop)
    (RelativeCupPresheaf.Constructions.relativeTwoCocycleOpenRestriction X C a U.unop)
    (RelativeCupPresheaf.Constructions.relativeTwoCocycleOpenRestriction X C b U.unop)
    (relativeOneCochainOpenRestriction_d X C v a b hv U.unop)

include hv in
theorem relativeTwoCupPresheafPrimitive_successor (n : ℕ) :
    (RelativeCupPresheaf.Constructions.relativeTwoCupPresheafComplexMap X C a).f (n+1) -
        (RelativeCupPresheaf.Constructions.relativeTwoCupPresheafComplexMap X C b).f (n+1) =
      (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).d (n+1) (n+2) ≫
        relativeOneCupSuccessorPresheafMap X C v (n+1) +
      relativeOneCupSuccessorPresheafMap X C v n ≫
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativePresheafComplex (ModuleCat.of ℚ ℚ) X C).d (2+n) (2+(n+1)) := by
  apply NatTrans.ext
  funext U
  exact RelativeCupHomotopy.Constructions.relativeTwoCupPrimitive_successor (TopCat.of U.unop) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C U.unop)
    (relativeOneCochainOpenRestriction X C v U.unop)
    (RelativeCupPresheaf.Constructions.relativeTwoCocycleOpenRestriction X C a U.unop)
    (RelativeCupPresheaf.Constructions.relativeTwoCocycleOpenRestriction X C b U.unop)
    (relativeOneCochainOpenRestriction_d X C v a b hv U.unop) n

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupPresheafHomotopy.Constructions
