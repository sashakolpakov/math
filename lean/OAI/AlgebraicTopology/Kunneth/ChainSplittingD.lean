import OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Homology.Homotopy

/-! # Chain Splitting D -/

namespace OAI.AlgebraicTopology.Kunneth.ChainSplittingD

noncomputable section

/-!
Linear splittings for the algebraic part of Kunneth. The splittings are chosen
using the projectivity of vector spaces; no homology or Künneth assertion
is assumed.
-/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives

namespace Construction.ChainSplitting

variable {k : Type} [Field k]
variable (C : ChainComplex (ModuleCat.{0} k) ℕ)

/-- Choose cycle representatives linearly for all homology classes. -/
def representatives (n : ℕ) : C.homology n →ₗ[k] Cohomology.Singular.ChainRepresentatives.chainCycles C n :=
  Classical.choose ((Cohomology.Singular.ChainRepresentatives.chainClass C n).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (Cohomology.Singular.ChainRepresentatives.chainClass_surjective C n)))

@[simp]
theorem class_representatives (n : ℕ) (a : C.homology n) :
    Cohomology.Singular.ChainRepresentatives.chainClass C n (representatives C n a) = a :=
  LinearMap.congr_fun
    (Classical.choose_spec ((Cohomology.Singular.ChainRepresentatives.chainClass C n).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (Cohomology.Singular.ChainRepresentatives.chainClass_surjective C n)))) a

/-- Extend the identity of the cycle subspace to a linear retraction. -/
def cycleRetraction (n : ℕ) : C.X n →ₗ[k] Cohomology.Singular.ChainRepresentatives.chainCycles C n :=
  (Cohomology.Singular.ChainRepresentatives.chainCycles C n).subtype.leftInverse

@[simp]
theorem cycleRetraction_cycle (n : ℕ) (z : Cohomology.Singular.ChainRepresentatives.chainCycles C n) :
    cycleRetraction C n z.val = z :=
  LinearMap.leftInverse_apply_of_inj (Cohomology.Singular.ChainRepresentatives.chainCycles C n).ker_subtype z

/-- The homology groups regarded as a chain complex with zero differential. -/
abbrev homologyComplex : ChainComplex (ModuleCat.{0} k) ℕ where
  X n := C.homology n
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := zero_comp

/-- Include the chosen homology representatives into the original complex. -/
def inclusion : homologyComplex C ⟶ C where
  f n := ModuleCat.ofHom ((Cohomology.Singular.ChainRepresentatives.chainCycles C n).subtype.comp (representatives C n))
  comm' i j _ := by
    rw [show (homologyComplex C).d i j = 0 from rfl, zero_comp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change (C.d i j) (representatives C i a).val = 0
    exact Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero C i j (representatives C i a)

/-- Project a chain onto cycles, then take its homology class. -/
def projection : C ⟶ homologyComplex C where
  f n := ModuleCat.ofHom ((Cohomology.Singular.ChainRepresentatives.chainClass C n).comp (cycleRetraction C n))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change 0 = Cohomology.Singular.ChainRepresentatives.chainClass C j (cycleRetraction C j ((C.d i j) x))
    have hcycle : (C.d i j) x ∈ Cohomology.Singular.ChainRepresentatives.chainCycles C j := by
      change (C.d j ((ComplexShape.down ℕ).next j)) ((C.d i j) x) = 0
      exact ConcreteCategory.congr_hom (C.d_comp_d i j _) x
    let z : Cohomology.Singular.ChainRepresentatives.chainCycles C j := ⟨(C.d i j) x, hcycle⟩
    have hz : cycleRetraction C j ((C.d i j) x) = z :=
      cycleRetraction_cycle C j z
    rw [hz]
    symm
    apply (Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff C j z).mpr
    have hij : i = j + 1 := ‹(ComplexShape.down ℕ).Rel i j›.symm
    subst i
    apply (Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff C j z).mp
    apply (Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists C j z).mpr
    exact ⟨x, rfl⟩

@[simp]
theorem inclusion_projection : inclusion C ≫ projection C = 𝟙 (homologyComplex C) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change Cohomology.Singular.ChainRepresentatives.chainClass C n
    (cycleRetraction C n (representatives C n a).val) = a
  rw [cycleRetraction_cycle, class_representatives]

/-- Remove the chosen homology component of a chain. -/
def remainder : C ⟶ C := 𝟙 C - projection C ≫ inclusion C

@[simp]
theorem remainder_projection : remainder C ≫ projection C = 0 := by
  simp [remainder, Category.assoc, inclusion_projection]

/-- The kernel of the projection, equipped with its induced differential. -/
abbrev acyclicPart : ChainComplex (ModuleCat.{0} k) ℕ where
  X n := ModuleCat.of k (LinearMap.ker ((projection C).f n).hom)
  d i j := ModuleCat.ofHom
    (((C.d i j).hom.comp (LinearMap.ker ((projection C).f i).hom).subtype).codRestrict
      (LinearMap.ker ((projection C).f j).hom) (by
        intro x
        change (projection C).f j ((C.d i j) x.val) = 0
        have h := ConcreteCategory.congr_hom ((projection C).comm i j) x.val
        simpa only [homologyComplex, ModuleCat.hom_comp, LinearMap.comp_apply,
          ModuleCat.hom_zero, LinearMap.zero_apply] using h.symm))
  shape i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (C.d i j) x.val = 0
    rw [C.shape i j hij]
    rfl
  d_comp_d' i j l _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (C.d_comp_d i j l) x.val

/-- Include the acyclic part in the original complex. -/
def acyclicInclusion : acyclicPart C ⟶ C where
  f n := ModuleCat.ofHom (LinearMap.ker ((projection C).f n).hom).subtype
  comm' _ _ _ := rfl

/-- Project a chain onto the kernel by removing its homology representative. -/
def acyclicProjection : C ⟶ acyclicPart C where
  f n := ModuleCat.ofHom (((remainder C).f n).hom.codRestrict
    (LinearMap.ker ((projection C).f n).hom) (by
      intro x
      exact ConcreteCategory.congr_hom
        (HomologicalComplex.congr_hom (remainder_projection C) n) x))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((remainder C).comm i j) x

@[simp]
theorem acyclicProjection_inclusion :
    acyclicProjection C ≫ acyclicInclusion C = remainder C := rfl

@[simp]
theorem remainder_on_kernel (n : ℕ)
    (x : LinearMap.ker ((projection C).f n).hom) :
    (remainder C).f n x.val = x.val := by
  change x.val - (inclusion C).f n ((projection C).f n x.val) = x.val
  rw [show (projection C).f n x.val = 0 from x.property, map_zero, sub_zero]

/-- Every cycle in the kernel is a boundary in that kernel. -/
theorem acyclicPart_cycle_is_boundary (n : ℕ)
    (x : Cohomology.Singular.ChainRepresentatives.chainCycles (acyclicPart C) n) :
    ∃ y : (acyclicPart C).X (n + 1),
      (acyclicPart C).d (n + 1) n y = x.val := by
  have hx : x.val.val ∈ Cohomology.Singular.ChainRepresentatives.chainCycles C n := by
    change (C.d n ((ComplexShape.down ℕ).next n)) x.val.val = 0
    exact congrArg Subtype.val x.property
  let z : Cohomology.Singular.ChainRepresentatives.chainCycles C n := ⟨x.val.val, hx⟩
  have hz : Cohomology.Singular.ChainRepresentatives.chainClass C n z = 0 := by
    have hp := x.val.property
    change Cohomology.Singular.ChainRepresentatives.chainClass C n (cycleRetraction C n z.val) = 0 at hp
    rwa [cycleRetraction_cycle] at hp
  obtain ⟨y, hy⟩ := (Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists C n z).mp hz
  refine ⟨(acyclicProjection C).f (n + 1) y, ?_⟩
  apply Subtype.ext
  change (C.d (n + 1) n) ((remainder C).f (n + 1) y) = x.val.val
  have hcomm := ConcreteCategory.congr_hom ((remainder C).comm (n + 1) n) y
  change (C.d (n + 1) n) ((remainder C).f (n + 1) y) =
    (remainder C).f n ((C.d (n + 1) n) y) at hcomm
  exact hcomm.trans ((congrArg ((remainder C).f n) hy).trans
    (remainder_on_kernel C n x.val))

/-- A linear choice of preimage for every vector in a differential's range. -/
def boundaryRangeSection (n : ℕ) :
    LinearMap.range (C.d (n + 1) n).hom →ₗ[k] C.X (n + 1) :=
  Classical.choose ((C.d (n + 1) n).hom.rangeRestrict.exists_rightInverse_of_surjective
    (C.d (n + 1) n).hom.range_rangeRestrict)

@[simp]
theorem boundaryRangeSection_d (n : ℕ)
    (z : LinearMap.range (C.d (n + 1) n).hom) :
    (C.d (n + 1) n) (boundaryRangeSection C n z) = z.val :=
  congrArg Subtype.val (LinearMap.congr_fun
    (Classical.choose_spec
      ((C.d (n + 1) n).hom.rangeRestrict.exists_rightInverse_of_surjective
        (C.d (n + 1) n).hom.range_rangeRestrict)) z)

section Acyclic

variable (hfill : ∀ (n : ℕ) (z : Cohomology.Singular.ChainRepresentatives.chainCycles C n),
  ∃ b : C.X (n + 1), (C.d (n + 1) n) b = z.val)

/-- Exactness over a field supplies a linear filling operator on cycles. -/
def fillCycles (n : ℕ) : Cohomology.Singular.ChainRepresentatives.chainCycles C n →ₗ[k] C.X (n + 1) :=
  (boundaryRangeSection C n).comp
    ((Cohomology.Singular.ChainRepresentatives.chainCycles C n).subtype.codRestrict
      (LinearMap.range (C.d (n + 1) n).hom) (hfill n))

@[simp]
theorem fillCycles_d (n : ℕ) (z : Cohomology.Singular.ChainRepresentatives.chainCycles C n) :
    (C.d (n + 1) n) (fillCycles C hfill n z) = z.val :=
  boundaryRangeSection_d C n _

/-- Fill a linear family of cycles, preserving linearity in its parameter. -/
def fillCycleMap {V : ModuleCat.{0} k} (n : ℕ) (f : V ⟶ C.X n)
    (hf : f ≫ C.d n ((ComplexShape.down ℕ).next n) = 0) :
    V ⟶ C.X (n + 1) :=
  ModuleCat.ofHom ((fillCycles C hfill n).comp
    (f.hom.codRestrict (Cohomology.Singular.ChainRepresentatives.chainCycles C n) (by
      intro x
      exact ConcreteCategory.congr_hom hf x)))

@[reassoc (attr := simp)]
theorem fillCycleMap_comp {V : ModuleCat.{0} k} (n : ℕ) (f : V ⟶ C.X n)
    (hf : f ≫ C.d n ((ComplexShape.down ℕ).next n) = 0) :
    fillCycleMap C hfill n f hf ≫ C.d (n + 1) n = f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact fillCycles_d C hfill n _

/-- A chain map into an acyclic complex of vector spaces is null-homotopic. -/
def nullhomotopy {P : ChainComplex (ModuleCat.{0} k) ℕ} (e : P ⟶ C) :
    Homotopy e 0 := by
  let hzero : e.f 0 ≫ C.d 0 ((ComplexShape.down ℕ).next 0) = 0 := by
    rw [C.shape 0 _ (Nat.succ_ne_zero _), comp_zero]
  let h0 := fillCycleMap C hfill 0 (e.f 0) hzero
  have h0eq : h0 ≫ C.d 1 0 = e.f 0 := fillCycleMap_comp C hfill 0 _ _
  have hclosed : (e.f 1 - P.d 1 0 ≫ h0) ≫
      C.d 1 ((ComplexShape.down ℕ).next 1) = 0 := by
    rw [ChainComplex.next_nat_succ]
    rw [Preadditive.sub_comp, Category.assoc, h0eq, e.comm 1 0, sub_self]
  let h1 := fillCycleMap C hfill 1 (e.f 1 - P.d 1 0 ≫ h0) hclosed
  have h1eq : h1 ≫ C.d 2 1 = e.f 1 - P.d 1 0 ≫ h0 :=
    fillCycleMap_comp C hfill 1 _ _
  refine Homotopy.mkInductive e h0 h0eq.symm h1 ?_ ?_
  · rw [h1eq]
    abel
  · intro n p
    rcases p with ⟨u, v, hp⟩
    let a := e.f (n + 2) - P.d (n + 2) (n + 1) ≫ v
    have ha : a ≫ C.d (n + 2) ((ComplexShape.down ℕ).next (n + 2)) = 0 := by
      rw [ChainComplex.next_nat_succ]
      dsimp only [a]
      rw [Preadditive.sub_comp, e.comm (n + 2) (n + 1), hp,
        Preadditive.comp_add]
      simp only [← Category.assoc, P.d_comp_d, zero_comp, zero_add, sub_self]
    refine ⟨fillCycleMap C hfill (n + 2) a ha, ?_⟩
    rw [fillCycleMap_comp]
    dsimp only [a]
    abel

end Acyclic

/-- The homology-free part contracts, and its contraction gives a homotopy
 between the identity and projection onto homology representatives. -/
def identityProjectionHomotopy : Homotopy (𝟙 C) (projection C ≫ inclusion C) := by
  have h := nullhomotopy (acyclicPart C) (acyclicPart_cycle_is_boundary C)
    (𝟙 (acyclicPart C))
  have hc := (h.compLeft (acyclicProjection C)).compRight (acyclicInclusion C)
  have hr : Homotopy (remainder C) 0 := by simpa using hc
  exact Homotopy.equivSubZero.symm hr

/-- Every chain complex of vector spaces is homotopy equivalent to its
 homology with zero differential. -/
def homologyHomotopyEquiv : HomotopyEquiv (homologyComplex C) C where
  hom := inclusion C
  inv := projection C
  homotopyHomInvId := Homotopy.ofEq (inclusion_projection C)
  homotopyInvHomId := (identityProjectionHomotopy C).symm

end Construction.ChainSplitting

end

end OAI.AlgebraicTopology.Kunneth.ChainSplittingD
