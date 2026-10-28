import OAI.AlgebraicGeometry.CycleClass.Geometric.ProjectiveComponentCycles
import OAI.AlgebraicGeometry.CycleClass.Geometric.SupportFiniteType
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.RingTheory.Length
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-! # Intersection Geometry -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry

noncomputable section

/-!
# Geometric operations used in ThomClass

This module does not import cohomology or the statement stubs. Rational
equivalence is the rational span of principal divisors on integral closed
subschemes. Proper intersections use the alternating lengths of the local
Tor modules (Serre's intersection multiplicity). An intersection representative
is obtained by moving the two inputs modulo rational equivalence, intersecting
properly, and again passing modulo rational equivalence.

Exterior products are formed from the reduced closed inverse-image
intersection in the product scheme, extended bilinearly to rational cycles.
The degree component of its fundamental cycle is used. Over the complex
numbers the product of the two reduced integral supports is reduced and has
the sum codimension, so its component multiplicities are one.

The definitions use no cohomological characterization. They do not prove the
moving lemma, descent of cycle classes, or either ThomClass compatibility theorem.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped BigOperators Classical

/-- The unique point generic in a closed integral support. -/
def supportPoint {X : Scheme} (W : IrreducibleCloseds X) : X :=
  irreducibleSetEquivPoints W

/-- Lift a point of the support to its reduced induced closed subscheme. -/
def supportPreimage {X : Scheme} (W : IrreducibleCloseds X)
    (x : X) (hx : x ∈ (W : Set X)) : Geometric.GenericPoint.reducedSupportScheme W :=
  Classical.choose ((Geometric.GenericPoint.range_reducedSupportι W).symm ▸ hx)

theorem supportPreimage_spec {X : Scheme} (W : IrreducibleCloseds X)
    (x : X) (hx : x ∈ (W : Set X)) :
    Geometric.GenericPoint.reducedSupportι W (supportPreimage W x hx) = x :=
  Classical.choose_spec ((Geometric.GenericPoint.range_reducedSupportι W).symm ▸ hx)

/-- The local ring of the integral closed support, as an ambient local module. -/
def localSupportModule (X : Scheme) (W : IrreducibleCloseds X)
    (x : X) (hx : x ∈ (W : Set X)) : ModuleCat (X.presheaf.stalk x) :=
  let y := supportPreimage W x hx
  let f : X.presheaf.stalk x ⟶ (Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk y :=
    eqToHom (congrArg (fun t => X.presheaf.stalk t)
      (supportPreimage_spec W x hx).symm) ≫ (Geometric.GenericPoint.reducedSupportι W).stalkMap y
  letI := f.hom.toAlgebra
  ModuleCat.of (X.presheaf.stalk x) ((Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk y)

/-- Length of the actual local Tor module of the two reduced supports. -/
def localTorLength (X : Scheme) (A B : IrreducibleCloseds X)
    (x : X) (hxA : x ∈ (A : Set X)) (hxB : x ∈ (B : Set X))
    (i : ℕ) : ℕ∞ :=
  Module.length (X.presheaf.stalk x)
    (((CategoryTheory.Tor (ModuleCat (X.presheaf.stalk x)) i).obj
      (localSupportModule X A x hxA)).obj (localSupportModule X B x hxB))

/-- Serre's local intersection multiplicity. The projective embedding dimension
 bounds the global dimension of the regular ambient local rings. At a
 generic point of a proper intersection the Tor modules have finite length.
 The definition is total: ENat.toNat assigns zero to infinite length.
 Finiteness and vanishing above the bound must be established when using
 this formula for proper intersections in the compatibility proof. -/
def intersectionMultiplicity (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A B C : IrreducibleCloseds X.carrier) : ℚ := by
  classical
  exact if h : supportPoint C ∈ (A : Set X.carrier) ∩ (B : Set X.carrier) then
    ∑ i ∈ Finset.range (X.ambientDimension + 1),
      (-1 : ℚ) ^ i *
        (localTorLength X.carrier A B (supportPoint C) h.1 h.2 i).toNat
  else 0

/-- Coefficient of the pushforward of div(f) from the reduced integral support.
 Its inclusion is a closed immersion, so residue-field degrees are one. -/
def principalDivisorCoefficient (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (W : IrreducibleCloseds X.carrier)
    (f : (Geometric.GenericPoint.reducedSupportScheme W).functionField)
    (C : IrreducibleCloseds X.carrier) : ℚ := by
  classical
  exact if h : supportPoint C ∈ (W : Set X.carrier) then
    ((Geometric.GenericPoint.reducedSupportScheme W).ord f (supportPreimage W (supportPoint C) h) : ℚ)
  else 0

/-- At the image of a support point, the coefficient is precisely its order
 of vanishing; the chosen preimage cannot change that coefficient. -/
theorem principalDivisorCoefficient_at_image (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (W : IrreducibleCloseds X.carrier)
    (f : (Geometric.GenericPoint.reducedSupportScheme W).functionField)
    (C : IrreducibleCloseds X.carrier) (x : Geometric.GenericPoint.reducedSupportScheme W)
    (hx : Geometric.GenericPoint.reducedSupportι W x = supportPoint C) :
    principalDivisorCoefficient X W f C = ((Geometric.GenericPoint.reducedSupportScheme W).ord f x : ℚ) := by
  have hmem : supportPoint C ∈ (W : Set X.carrier) := by
    rw [← Geometric.GenericPoint.range_reducedSupportι W]
    exact ⟨x, hx⟩
  have he : supportPreimage W (supportPoint C) hmem = x :=
    (Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective
      ((supportPreimage_spec W (supportPoint C) hmem).trans hx.symm)
  simp only [principalDivisorCoefficient, dite_eq_left hmem, he]

/-- A finite cycle is a principal-divisor generator exactly when its
 coefficients are the orders of a nonzero rational function on a
 codimension-(p-1) integral closed subscheme. -/
def IsPrincipalDivisor (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (d : X.RationalDimensionCycle p) : Prop :=
  ∃ W : IrreducibleCloseds X.carrier,
    X.supportCodimension W + 1 = p ∧
      ∃ f : (Geometric.GenericPoint.reducedSupportScheme W).functionField,
        f ≠ 0 ∧ ∀ C : X.DimensionCycleSupport p,
          d C = principalDivisorCoefficient X W f C.val

/-- The usual subgroup of rational equivalences with rational coefficients. -/
def rationalEquivalences (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) :
    Submodule ℚ (X.RationalDimensionCycle p) :=
  Submodule.span ℚ {d | IsPrincipalDivisor X p d}

def RationallyEquivalent (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (a b : X.RationalDimensionCycle p) : Prop :=
  a - b ∈ rationalEquivalences X p

/-- Rational Chow groups, as the quotient by the explicitly defined divisors. -/
abbrev ChowQ (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) :=
  X.RationalDimensionCycle p ⧸ rationalEquivalences X p

theorem rationallyEquivalent_refl (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (a : X.RationalDimensionCycle p) : RationallyEquivalent X p a a := by
  simp [RationallyEquivalent]

theorem rationallyEquivalent_symm (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    {a b : X.RationalDimensionCycle p} (h : RationallyEquivalent X p a b) :
    RationallyEquivalent X p b a := by
  simpa only [RationallyEquivalent, neg_sub] using
    (rationalEquivalences X p).neg_mem h

theorem rationallyEquivalent_trans (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    {a b c : X.RationalDimensionCycle p}
    (hab : RationallyEquivalent X p a b) (hbc : RationallyEquivalent X p b c) :
    RationallyEquivalent X p a c := by
  simpa only [RationallyEquivalent, sub_add_sub_cancel] using
    (rationalEquivalences X p).add_mem hab hbc

theorem rationallyEquivalent_iff_chow_eq (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (a b : X.RationalDimensionCycle p) :
    RationallyEquivalent X p a b ↔
      (Submodule.Quotient.mk a : ChowQ X p) = Submodule.Quotient.mk b := by
  exact (Submodule.Quotient.eq (rationalEquivalences X p)).symm

/-- All pairs of supports with nonzero coefficients intersect properly. -/
def MeetProperly (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q) : Prop :=
  ∀ A ∈ a.support, ∀ B ∈ b.support,
    ∀ C : IrreducibleCloseds X.carrier,
      (C : Set X.carrier) ⊆ (A.val : Set X.carrier) ∩ (B.val : Set X.carrier) →
        p + q ≤ X.supportCodimension C

/-- The actual proper-intersection cycle, specified coefficient by coefficient
 by the bilinear extension of Serre's local multiplicities. -/
def IsProperIntersectionCycle (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (c : X.RationalDimensionCycle (p + q)) : Prop :=
  MeetProperly X p q a b ∧
    ∀ C : X.DimensionCycleSupport (p + q),
      c C = a.sum (fun A r => b.sum (fun B s =>
        r * s * intersectionMultiplicity X A.val B.val C.val))

theorem isProperIntersectionCycle_unique
    (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    {a : X.RationalDimensionCycle p} {b : X.RationalDimensionCycle q}
    {c d : X.RationalDimensionCycle (p + q)}
    (hc : IsProperIntersectionCycle X p q a b c)
    (hd : IsProperIntersectionCycle X p q a b d) : c = d := by
  exact Finsupp.ext fun C => (hc.2 C).trans (hd.2 C).symm

/-- [c] = [a] · [b] in the Chow group, using rationally equivalent
 properly intersecting representatives and the geometric multiplicities. -/
def RepresentsIntersection (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (c : X.RationalDimensionCycle (p + q)) : Prop :=
  ∃ (a' : X.RationalDimensionCycle p) (b' : X.RationalDimensionCycle q)
      (c' : X.RationalDimensionCycle (p + q)),
    RationallyEquivalent X p a a' ∧ RationallyEquivalent X q b b' ∧
      IsProperIntersectionCycle X p q a' b' c' ∧
        RationallyEquivalent X (p + q) c c'

/-- A proper intersection already provides a representative of the Chow product. -/
theorem representsIntersection_of_proper
    (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (c : X.RationalDimensionCycle (p + q))
    (h : IsProperIntersectionCycle X p q a b c) :
    RepresentsIntersection X p q a b c :=
  ⟨a, b, c, rationallyEquivalent_refl X p a,
    rationallyEquivalent_refl X q b, h, rationallyEquivalent_refl X (p + q) c⟩

/-- An irreducible component of a closed subset, as an ambient closed support. -/
def closedComponentSupport (X : Scheme) (S : Closeds X)
    (C : irreducibleComponents S) : IrreducibleCloseds X where
  carrier := Subtype.val '' C.val
  isIrreducible' := C.property.1.image Subtype.val continuous_subtype_val.continuousOn
  isClosed' := S.isClosed.isClosedMap_subtype_val _
    (isClosed_of_mem_irreducibleComponents C.val C.property)

/-- Distinct geometric components receive distinct support labels. -/
theorem closedComponentSupport_injective (X : Scheme) (S : Closeds X) :
    Function.Injective (closedComponentSupport X S) := by
  intro C D h
  apply Subtype.ext
  apply (Set.image_injective.mpr Subtype.val_injective)
  exact congrArg (fun W : IrreducibleCloseds X => (W : Set X)) h

/-- Retain an integral support in its prescribed codimension. -/
def supportInDegree (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (W : IrreducibleCloseds X.carrier) : X.RationalDimensionCycle p := by
  classical
  exact if h : X.supportCodimension W = p then Finsupp.single ⟨W, h⟩ 1 else 0

theorem supportInDegree_apply (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (W : IrreducibleCloseds X.carrier) (C : X.DimensionCycleSupport p) :
    supportInDegree X p W C = if W = C.val then 1 else 0 := by
  classical
  by_cases h : W = C.val
  · subst W
    simp only [supportInDegree, dite_eq_left C.property, ite_true]
    change (Finsupp.single C (1 : ℚ)) C = 1
    exact Finsupp.single_eq_same
  · by_cases hW : X.supportCodimension W = p
    · simp only [supportInDegree, dite_eq_left hW, ite_eq_right h]
      change (Finsupp.single (⟨W, hW⟩ : X.DimensionCycleSupport p) (1 : ℚ)) C = 0
      exact Finsupp.single_eq_of_ne' (fun he => h (congrArg
        (fun D : X.DimensionCycleSupport p => D.val) he))
    · simp [supportInDegree, hW, h]

/-- The degree-p part of the fundamental cycle of the reduced closed subset. -/
def reducedClosedCycle (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (S : Closeds X.carrier) : X.RationalDimensionCycle p := by
  classical
  letI : NoetherianSpace S := NoetherianSpace.set (S : Set X.carrier)
  letI : Finite (irreducibleComponents S) :=
    (NoetherianSpace.finite_irreducibleComponents (α := S)).to_subtype
  letI := Fintype.ofFinite (irreducibleComponents S)
  exact ∑ C : irreducibleComponents S,
    supportInDegree X p (closedComponentSupport X.carrier S C)

/-- Every component of the requested degree occurs exactly once with
 coefficient one, and all other supports have coefficient zero. -/
theorem reducedClosedCycle_apply (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (S : Closeds X.carrier) (W : X.DimensionCycleSupport p) :
    reducedClosedCycle X p S W =
      if ∃ C : irreducibleComponents S,
        closedComponentSupport X.carrier S C = W.val then 1 else 0 := by
  classical
  let : NoetherianSpace S := NoetherianSpace.set (S : Set X.carrier)
  let : Finite (irreducibleComponents S) :=
    (NoetherianSpace.finite_irreducibleComponents (α := S)).to_subtype
  let := Fintype.ofFinite (irreducibleComponents S)
  simp only [reducedClosedCycle, Finsupp.finsetSum_apply, supportInDegree_apply]
  by_cases h : ∃ C : irreducibleComponents S,
      closedComponentSupport X.carrier S C = W.val
  · obtain ⟨C, hC⟩ := h
    rw [ite_eq_left ⟨C, hC⟩]
    have he (D : irreducibleComponents S) :
        closedComponentSupport X.carrier S D = W.val ↔ D = C := by
      rw [← hC]
      exact (closedComponentSupport_injective X.carrier S).eq_iff
    simp_rw [he]
    simp
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro C _
    exact ite_eq_right (fun hC => h ⟨C, hC⟩)

/-- Under the product projections this closed subset is the product of the
 two closed supports, with its reduced induced scheme structure. -/
def productClosedSupport
    (X Y Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
    (A : IrreducibleCloseds X.carrier) (B : IrreducibleCloseds Y.carrier) :
    Closeds Z.carrier :=
  ⟨πX.left ⁻¹' (A : Set X.carrier) ∩ πY.left ⁻¹' (B : Set Y.carrier),
    (A.isClosed.preimage πX.left.continuous).inter
      (B.isClosed.preimage πY.left.continuous)⟩

/-- The geometric exterior product of rational cycles. -/
def exteriorCycleProduct
    (X Y Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
    (hprod : IsLimit (BinaryFan.mk πX πY)) (p q : ℕ)
    (a : X.RationalDimensionCycle p) (b : Y.RationalDimensionCycle q) :
    Z.RationalDimensionCycle (p + q) :=
  let _productWitness := hprod
  a.sum (fun A r => b.sum (fun B s =>
    (r * s) • reducedClosedCycle Z (p + q)
      (productClosedSupport X Y Z πX πY A.val B.val)))

theorem exteriorCycleProduct_single
    (X Y Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
    (hprod : IsLimit (BinaryFan.mk πX πY)) (p q : ℕ)
    (A : X.DimensionCycleSupport p) (B : Y.DimensionCycleSupport q) (r s : ℚ) :
    exteriorCycleProduct X Y Z πX πY hprod p q
        (Finsupp.single A r) (Finsupp.single B s) =
      (r * s) • reducedClosedCycle Z (p + q)
        (productClosedSupport X Y Z πX πY A.val B.val) := by
  simp [exteriorCycleProduct, Finsupp.sum_single_index]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry
