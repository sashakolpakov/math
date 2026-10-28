import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeSplitting
import Mathlib.Algebra.Group.MinimalAxioms

/-! # Split Group -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SplitGroup.SplitGroupLabels

noncomputable section

/-! Recover the group operations on finite labels from an actual scheme
splitting. Naturality forces these operations to act pointwise; their
finite tables are locally constant on the splitting base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Topology

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

variable {S : Scheme.{0}} {I : Type} {H : Over S}
  (e : HilbertConstruction.ConstantScheme.Iff.constantScheme S I ≅ H)

def label (T : Over S) (f : T ⟶ H) : LocallyConstant T.left I :=
  HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S I T (f ≫ e.inv)

theorem label_injective (T : Over S) : Function.Injective (label e T) := by
  intro f g h
  exact (cancel_mono e.inv).mp ((HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S I T).injective h)

def pointEquiv (T : Over S) : (T ⟶ H) ≃ LocallyConstant T.left I where
  toFun := label e T
  invFun c := (HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S I T).symm c ≫ e.hom
  left_inv f := by
    change (HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S I T).symm
      (HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S I T (f ≫ e.inv)) ≫ e.hom = f
    rw [Equiv.symm_apply_apply, Category.assoc, e.inv_hom_id, Category.comp_id]
  right_inv c := by
    change HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S I T
      (((HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S I T).symm c ≫ e.hom) ≫ e.inv) = c
    rw [Category.assoc, e.hom_inv_id, Category.comp_id, Equiv.apply_symm_apply]

def sectionOf (i : I) : ConstantSectionsOn.ConstantSections.baseTest S ⟶ H := ConstantSectionsOn.ConstantSections.component S i ≫ e.hom

theorem label_natural {T U : Over S} (j : U ⟶ T) (f : T ⟶ H) :
    label e U (j ≫ f) = (label e T f).comap ⟨j.left, j.left.continuous⟩ := rfl

theorem label_section (i : I) : label e (ConstantSectionsOn.ConstantSections.baseTest S) (sectionOf e i) =
    LocallyConstant.const S i := by
  have hw : sectionOf e i ≫ e.inv = ConstantSectionsOn.ConstantSections.component S i := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => ConstantSectionsOn.ConstantSections.component S i ≫ f) e.hom_inv_id).trans (Category.comp_id _))
  change HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S I (ConstantSectionsOn.ConstantSections.baseTest S) (sectionOf e i ≫ e.inv) = _
  rw [hw]
  apply LocallyConstant.ext
  intro x
  exact HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex_ι i x

/-- Over a fiber of the label function, a section is the corresponding
constant section, as an equality of scheme morphisms. -/
theorem restrict_eq_section (T : Over S) (x : T ⟶ H) (i : I)
    {U : Over S} (j : U ⟶ T)
    (hx : (label e T x).comap ⟨j.left, j.left.continuous⟩ =
      LocallyConstant.const U.left i) :
    j ≫ x = ConstantSectionsOn.ConstantSections.toBase U ≫ sectionOf e i := by
  apply label_injective e U
  rw [label_natural, label_natural, label_section, hx]
  rfl

variable [GrpObj H]

def productLabel (i j : I) : LocallyConstant S I :=
  label e (ConstantSectionsOn.ConstantSections.baseTest S) (sectionOf e i * sectionOf e j)

def unitLabel : LocallyConstant S I := label e (ConstantSectionsOn.ConstantSections.baseTest S) 1

def inverseLabel (i : I) : LocallyConstant S I :=
  label e (ConstantSectionsOn.ConstantSections.baseTest S) (sectionOf e i)⁻¹

/-- Multiplication at any test point is obtained from the table of
products of constant sections at its image in the base. -/
theorem label_mul (T : Over S) (x y : T ⟶ H) (t : T.left) :
    label e T (x * y) t =
      productLabel e (label e T x t) (label e T y t) (T.hom t) := by
  let c := label e T x
  let d := label e T y
  let p : LocallyConstant T.left (I × I) :=
    ⟨fun z => (c z, d z), c.isLocallyConstant.prodMk d.isLocallyConstant⟩
  let i := (c t, d t)
  let U := ConstantSectionsOn.ConstantSections.fiberTest T p i
  let j := ConstantSectionsOn.ConstantSections.fiberInclusion T p i
  let u : U.left := ⟨t, rfl⟩
  have hx : j ≫ x = ConstantSectionsOn.ConstantSections.toBase U ≫ sectionOf e i.1 := by
    apply restrict_eq_section
    apply LocallyConstant.ext
    intro z
    exact congrArg Prod.fst z.property
  have hy : j ≫ y = ConstantSectionsOn.ConstantSections.toBase U ≫ sectionOf e i.2 := by
    apply restrict_eq_section
    apply LocallyConstant.ext
    intro z
    exact congrArg Prod.snd z.property
  have hm : j ≫ (x * y) = ConstantSectionsOn.ConstantSections.toBase U ≫ (sectionOf e i.1 * sectionOf e i.2) := by
    rw [MonObj.comp_mul, hx, hy, MonObj.comp_mul]
  have hl := congrArg (fun f : U ⟶ H => label e U f u) hm
  exact hl

theorem label_one (T : Over S) (t : T.left) :
    label e T 1 t = unitLabel e (T.hom t) := by
  have h : ConstantSectionsOn.ConstantSections.toBase T ≫ (1 : ConstantSectionsOn.ConstantSections.baseTest S ⟶ H) = 1 := MonObj.comp_one _
  exact (congrArg (fun f : T ⟶ H => label e T f t) h).symm

/-- A finite operation table is locally constant in its entirety. -/
def operationTable [Finite I] : LocallyConstant S (I × (I → I) × (I → I → I)) where
  toFun s := (unitLabel e s, (fun i => inverseLabel e i s), fun i j => productLabel e i j s)
  isLocallyConstant := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro s
    have h1 := (unitLabel e).isLocallyConstant.eventually_eq s
    have hi : ∀ᶠ t in 𝓝 s, ∀ i, inverseLabel e i t = inverseLabel e i s :=
      Filter.eventually_all.mpr (fun i => (inverseLabel e i).isLocallyConstant.eventually_eq s)
    have hm : ∀ᶠ t in 𝓝 s, ∀ i j, productLabel e i j t = productLabel e i j s :=
      Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr
        (fun j => (productLabel e i j).isLocallyConstant.eventually_eq s))
    filter_upwards [h1, hi, hm] with t ht1 hti htm
    exact Prod.ext ht1 (Prod.ext (funext hti) (funext fun i => funext (htm i)))

/-- The actual group laws imply the group axioms for the table at every
base point. No group structure on the finite label set is supplied. -/
@[instance_reducible]
def groupAt (s : S) : Group I := by
  letI : One I := ⟨unitLabel e s⟩
  letI : Mul I := ⟨fun i j => productLabel e i j s⟩
  letI : Inv I := ⟨fun i => inverseLabel e i s⟩
  apply Group.ofLeftAxioms
  · intro a b c
    have h := congrArg (fun f : ConstantSectionsOn.ConstantSections.baseTest S ⟶ H => label e (ConstantSectionsOn.ConstantSections.baseTest S) f s)
      (mul_assoc (sectionOf e a) (sectionOf e b) (sectionOf e c))
    simp only [label_mul, label_section] at h
    exact h
  · intro a
    have h := congrArg (fun f : ConstantSectionsOn.ConstantSections.baseTest S ⟶ H => label e (ConstantSectionsOn.ConstantSections.baseTest S) f s)
      (one_mul (sectionOf e a))
    simp only [label_mul, label_one, label_section] at h
    exact h
  · intro a
    have h := congrArg (fun f : ConstantSectionsOn.ConstantSections.baseTest S ⟶ H => label e (ConstantSectionsOn.ConstantSections.baseTest S) f s)
      (inv_mul_cancel (sectionOf e a))
    simp only [label_mul, label_one, label_section] at h
    exact h

def tableNeighborhood [Finite I] (s : S) : S.Opens :=
  HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (operationTable e) (operationTable e s)

theorem mem_tableNeighborhood [Finite I] (s : S) : s ∈ tableNeighborhood e s := rfl

/-- On a test lying in the fixed-table neighborhood, the representing
equivalence is an equivalence of groups. -/
def labelMulEquiv [Finite I] (s : S) (T : Over S)
    (hT : ∀ t : T.left, operationTable e (T.hom t) = operationTable e s) :
    letI := groupAt e s
    (T ⟶ H) ≃* LocallyConstant T.left I := by
  letI := groupAt e s
  refine { pointEquiv e T with map_mul' := ?_ }
  intro x y
  apply LocallyConstant.ext
  intro t
  change label e T (x * y) t = productLabel e (label e T x t) (label e T y t) s
  exact (label_mul e T x y t).trans
    (congrArg (fun a : I × (I → I) × (I → I → I) =>
      a.2.2 (label e T x t) (label e T y t)) (hT t))

/-- Every finite scheme splitting refines to an actual local group
trivialization, with its finite group constructed from the fiber table. -/
def localGroupIso [Finite I] (s : S) :
    letI := groupAt e s
    HilbertConstruction.Constant.GroupMaps.constantGroupFunctor (tableNeighborhood e s).toScheme I ≅
      (Over.map (tableNeighborhood e s).ι).op ⋙ yonedaGrpObj H := by
  letI := groupAt e s
  let U := tableNeighborhood e s
  let eqv (T : Over U.toScheme) := labelMulEquiv e s ((Over.map U.ι).obj T)
    (fun t => (T.hom t).property)
  refine NatIso.ofComponents (fun T => MulEquiv.toGrpIso (eqv T.unop).symm) ?_
  intro T V f
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro c
  apply (eqv V.unop).injective
  change eqv V.unop ((eqv V.unop).symm
      (c.comap ⟨f.unop.left, f.unop.left.continuous⟩)) =
    label e ((Over.map U.ι).obj V.unop)
      ((Over.map U.ι).map f.unop ≫ (eqv T.unop).symm c)
  rw [MulEquiv.apply_symm_apply, label_natural]
  exact (congrArg (fun d : LocallyConstant T.unop.left I =>
    d.comap ⟨f.unop.left, f.unop.left.continuous⟩) ((eqv T.unop).apply_symm_apply c)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SplitGroup.SplitGroupLabels
