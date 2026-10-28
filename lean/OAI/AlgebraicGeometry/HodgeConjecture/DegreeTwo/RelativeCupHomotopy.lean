import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CupConnectingComponent
import Mathlib.Algebra.Homology.Embedding.TruncGEHomology

/-! # Relative Cup Homotopy -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions

noncomputable section

section

/-! Cup with an actual relative degree-two cocycle defines a natural map to the canonically truncated shifted complex. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false

def cochainDegreeShiftEmbedding (k : ℕ) : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
  ComplexShape.Embedding.mk' _ _ (fun n => k+n) (fun _ _ h => Nat.add_left_cancel h)
    (by intro i j; change (i+1=j) ↔ (k+i+1=k+j); omega)

instance cochainDegreeShiftEmbedding_isRelIff (k : ℕ) : (cochainDegreeShiftEmbedding k).IsRelIff := by
  unfold cochainDegreeShiftEmbedding
  infer_instance

instance cochainDegreeShiftEmbedding_isTruncGE (k : ℕ) : (cochainDegreeShiftEmbedding k).IsTruncGE where
  mem_next {j l} h := by
    refine ⟨j+1,?_⟩
    change k+j+1=l at h
    change k+(j+1)=l
    omega

variable (X : TopCat.{0}) (C : Set X)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) 2)

def relativeTwoCupCochainMap :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X ⟶
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).restriction (cochainDegreeShiftEmbedding 2) where
  f n := ModuleCat.ofHom (CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X C 2 n a.val)
  comm' i j hij := by
    have hj : i+1=j := hij
    subst j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    change (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).d (2+i) (2+(i+1))
        (CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X C 2 i a.val b) =
      CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X C 2 (i+1) a.val ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d i (i+1) b)
    apply CycleClass.Geometric.RelativeCochainHomotopy.Cohomology.relativeCochainInclusion_injective (ModuleCat.of ℚ ℚ) X C (2+(i+1))
    rw [SupportCupDifferential.Constructions.relativeCochainInclusion_d_apply]
    simp only [CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup, CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCupWith_inclusion]
    exact CupConnectingComponent.Constructions.relativeDegreeTwoCup_d X C i a b

def relativeTwoCupGoodShiftMap :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X ⟶
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).truncGE' (cochainDegreeShiftEmbedding 2) :=
  relativeTwoCupCochainMap X C a ≫
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).restrictionToTruncGE' (cochainDegreeShiftEmbedding 2)

theorem relativeTwoCupCochainMap_naturality {Y : TopCat.{0}} (f : Y ⟶ X)
    (D : Set Y) (hf : Set.MapsTo f D C) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) f ≫
      relativeTwoCupCochainMap Y D
        (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f hf) 2 a) =
    relativeTwoCupCochainMap X C a ≫
      HomologicalComplex.restrictionMap (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f hf)
        (cochainDegreeShiftEmbedding 2) := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  change CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup Y D 2 n
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f hf).f 2 a.val)
      ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) f).f n b) =
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f hf).f (2+n)
      (CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X C 2 n a.val b)
  exact (CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCupWith_pullback Y D
    (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
    (LinearMap.mul ℚ ℚ) f hf a.val b).symm

end

section

/-! The good degree-two shift retains cochain homotopies, including the initial boundary. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive _root_.HomologicalComplex Homotopy

set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Category C] [Abelian C]

def cochainHomotopyComponents {A B : CochainComplex C ℕ}
    (h : ∀ n, A.X (n+1) ⟶ B.X n) (i j : ℕ) : A.X i ⟶ B.X j :=
  if hij : i=j+1 then eqToHom (congrArg A.X hij) ≫ h j else 0

theorem cochainHomotopyComponents_succ {A B : CochainComplex C ℕ}
    (h : ∀ n, A.X (n+1) ⟶ B.X n) (n : ℕ) :
    cochainHomotopyComponents h (n+1) n = h n := by
  simp [cochainHomotopyComponents]

def cochainHomotopyFromSuccessor {A B : CochainComplex C ℕ} (f g : A ⟶ B)
    (h : ∀ n, A.X (n+1) ⟶ B.X n)
    (hzero : f.f 0 = A.d 0 1 ≫ h 0 + g.f 0)
    (hsucc : ∀ n, f.f (n+1) = A.d (n+1) (n+2) ≫ h (n+1) +
      h n ≫ B.d n (n+1) + g.f (n+1)) : Homotopy f g where
  hom := cochainHomotopyComponents h
  zero i j hij := by
    apply dite_eq_right
    change ¬ (j+1=i) at hij
    exact Ne.symm hij
  comm n := by
    rw [dNext_cochainComplex, cochainHomotopyComponents_succ]
    cases n with
    | zero => rw [prevD_zero_cochainComplex, add_zero]; exact hzero
    | succ n =>
      rw [prevD_succ_cochainComplex, cochainHomotopyComponents_succ]
      exact hsucc n

theorem cochainTwoGoodShift_initial_boundary (B : CochainComplex C ℕ) :
    B.d 1 2 ≫ (B.restrictionToTruncGE' (cochainDegreeShiftEmbedding 2)).f 0 = 0 := by
  have hb : (cochainDegreeShiftEmbedding 2).BoundaryGE 0 :=
    (cochainDegreeShiftEmbedding 2).boundaryGE (i' := 1) rfl
      (by intro n; change 2+n≠1; omega)
  rw [B.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv
    (cochainDegreeShiftEmbedding 2) rfl hb]
  change B.d 1 2 ≫ 𝟙 _ ≫ B.pOpcycles 2 ≫ _ = 0
  rw [Category.id_comp, ← Category.assoc, B.d_pOpcycles, zero_comp]

/-- A primitive in the discarded degree is killed by the canonical quotient. -/
def cochainTwoGoodShiftHomotopy {A B : CochainComplex C ℕ}
    (f g : A ⟶ B.restriction (cochainDegreeShiftEmbedding 2))
    (h : ∀ n, A.X (n+1) ⟶ B.X (2+n)) (v : A.X 0 ⟶ B.X 1)
    (hzero : f.f 0 - g.f 0 = A.d 0 1 ≫ h 0 + v ≫ B.d 1 2)
    (hsucc : ∀ n, f.f (n+1) - g.f (n+1) =
      A.d (n+1) (n+2) ≫ h (n+1) + h n ≫ B.d (2+n) (2+(n+1))) :
    Homotopy (f ≫ B.restrictionToTruncGE' (cochainDegreeShiftEmbedding 2))
      (g ≫ B.restrictionToTruncGE' (cochainDegreeShiftEmbedding 2)) := by
  let t := B.restrictionToTruncGE' (cochainDegreeShiftEmbedding 2)
  apply cochainHomotopyFromSuccessor _ _ (fun n => h n ≫ t.f n)
  · have hz := congrArg (fun m => m ≫ t.f 0) hzero
    simp only [sub_comp, add_comp, Category.assoc] at hz
    rw [cochainTwoGoodShift_initial_boundary, comp_zero, add_zero] at hz
    exact sub_eq_iff_eq_add.mp hz
  · intro n
    have hs := congrArg (fun m => m ≫ t.f (n+1)) (hsucc n)
    have ht : B.d (2+n) (2+(n+1)) ≫ t.f (n+1) =
        t.f n ≫ (B.truncGE' (cochainDegreeShiftEmbedding 2)).d n (n+1) :=
      (t.comm n (n+1)).symm
    simp only [sub_comp, add_comp, Category.assoc] at hs
    rw [ht, ← Category.assoc (h n)] at hs
    exact sub_eq_iff_eq_add.mp hs

end

/-! Cup by a relative coboundary gives an actual homotopy after good truncation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (C : Set X)
variable (v : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).X 1)

theorem relativeCochainCast_trans {i j k : ℕ} (h : i=j) (h' : j=k)
    (b : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).X i) :
    CycleClass.Geometric.RelativeCup.Cycles.relativeCochainCast (ModuleCat.of ℚ ℚ) X C h'
        (CycleClass.Geometric.RelativeCup.Cycles.relativeCochainCast (ModuleCat.of ℚ ℚ) X C h b) =
      CycleClass.Geometric.RelativeCup.Cycles.relativeCochainCast (ModuleCat.of ℚ ℚ) X C (h.trans h') b := by
  subst j k
  rfl

theorem relativeCochainCast_d {i j i' j' : ℕ} (hi : i=i') (hj : j=j')
    (b : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).X i) :
    CycleClass.Geometric.RelativeCup.Cycles.relativeCochainCast (ModuleCat.of ℚ ℚ) X C hj
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).d i j b) =
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).d i' j'
        (CycleClass.Geometric.RelativeCup.Cycles.relativeCochainCast (ModuleCat.of ℚ ℚ) X C hi b) := by
  subst i' j'
  rfl

def relativeOneCupSuccessorMap (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X (n+1) ⟶
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).X (2+n) :=
  ModuleCat.ofHom ((CycleClass.Geometric.RelativeCup.Cycles.relativeCochainCast (ModuleCat.of ℚ ℚ) X C (by omega : 1+(n+1)=2+n)).comp
    (CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X C 1 (n+1) v))

def relativeOneCupZeroMap :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X 0 ⟶
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).X 1 :=
  ModuleCat.ofHom (CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X C 1 0 v)

theorem relativeOneCup_coboundary (q : ℕ)
    (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X q) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).d (1+q) (1+q+1)
        (CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X C 1 q v b) =
      CycleClass.Geometric.RelativeCup.Cycles.relativeCochainCast (ModuleCat.of ℚ ℚ) X C (by omega : 2+q=1+q+1)
        (CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X C 2 q
          ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).d 1 2 v) b) -
      CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X C 1 (q+1) v
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d q (q+1) b) := by
  have h := CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCupWith_coboundary X C
    (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
    (LinearMap.mul ℚ ℚ) v b
  simpa only [CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup, pow_one, neg_one_zsmul, sub_eq_add_neg] using h

theorem relativeOneCup_zero_identity
    (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X 0) :
    CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X C 2 0
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).d 1 2 v) b =
      relativeOneCupSuccessorMap X C v 0
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d 0 1 b) +
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).d 1 2
        (relativeOneCupZeroMap X C v b) := by
  have h := relativeOneCup_coboundary X C v 0 b
  change _ = CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X C 1 1 v
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d 0 1 b) +
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).d 1 2
      (CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X C 1 0 v b)
  exact (sub_eq_iff_eq_add.mp h.symm).trans (add_comm _ _)

theorem relativeOneCup_successor_identity (n : ℕ)
    (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X (n+1)) :
    CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X C 2 (n+1)
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).d 1 2 v) b =
      relativeOneCupSuccessorMap X C v (n+1)
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d (n+1) (n+2) b) +
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).d (2+n) (2+(n+1))
        (relativeOneCupSuccessorMap X C v n b) := by
  have h := relativeOneCup_coboundary X C v (n+1) b
  have ht := congrArg (CycleClass.Geometric.RelativeCup.Cycles.relativeCochainCast (ModuleCat.of ℚ ℚ) X C
    (by omega : 1+(n+1)+1=2+(n+1)))
    ((sub_eq_iff_eq_add.mp h.symm).trans (add_comm _ _))
  rw [relativeCochainCast_trans, CycleClass.Geometric.RelativeCup.Cycles.relativeCochainCast_rfl, map_add,
    relativeCochainCast_d X C (by omega : 1+(n+1)=2+n)] at ht
  exact ht

theorem relativeTwoCup_sub_left (q : ℕ)
    (a b : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).X 2)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X q) :
    CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X C 2 q a c - CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X C 2 q b c =
      CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X C 2 q (a-b) c := by
  rw [map_sub, LinearMap.sub_apply]

theorem relativeTwoCupPrimitive_zero
    (a b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) 2)
    (hv : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).d 1 2 v = a.val-b.val) :
    (relativeTwoCupCochainMap X C a).f 0 - (relativeTwoCupCochainMap X C b).f 0 =
      (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d 0 1 ≫ relativeOneCupSuccessorMap X C v 0 +
        relativeOneCupZeroMap X C v ≫ (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).d 1 2 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X C 2 0 a.val c - CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X C 2 0 b.val c =
      relativeOneCupSuccessorMap X C v 0 ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d 0 1 c) +
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).d 1 2 (relativeOneCupZeroMap X C v c)
  rw [relativeTwoCup_sub_left, ← hv]
  exact relativeOneCup_zero_identity X C v c

theorem relativeTwoCupPrimitive_successor
    (a b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) 2)
    (hv : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).d 1 2 v = a.val-b.val) (n : ℕ) :
    (relativeTwoCupCochainMap X C a).f (n+1) - (relativeTwoCupCochainMap X C b).f (n+1) =
      (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d (n+1) (n+2) ≫ relativeOneCupSuccessorMap X C v (n+1) +
        relativeOneCupSuccessorMap X C v n ≫
          (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).d (2+n) (2+(n+1)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X C 2 (n+1) a.val c - CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X C 2 (n+1) b.val c =
      relativeOneCupSuccessorMap X C v (n+1)
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d (n+1) (n+2) c) +
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).d (2+n) (2+(n+1))
        (relativeOneCupSuccessorMap X C v n c)
  rw [relativeTwoCup_sub_left, ← hv]
  exact relativeOneCup_successor_identity X C v n c

def relativeTwoCupGoodShiftHomotopy
    (a b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) 2)
    (hv : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C).d 1 2 v = a.val-b.val) :
    Homotopy (relativeTwoCupGoodShiftMap X C a) (relativeTwoCupGoodShiftMap X C b) :=
  cochainTwoGoodShiftHomotopy (relativeTwoCupCochainMap X C a)
    (relativeTwoCupCochainMap X C b) (relativeOneCupSuccessorMap X C v)
    (relativeOneCupZeroMap X C v) (relativeTwoCupPrimitive_zero X C v a b hv)
    (relativeTwoCupPrimitive_successor X C v a b hv)

theorem relativeTwoCupGoodShift_homologyMap_eq
    (a b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) 2)
    (hab : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) 2 a =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) 2 b) (n : ℕ) :
    HomologicalComplex.homologyMap (relativeTwoCupGoodShiftMap X C a) n =
      HomologicalComplex.homologyMap (relativeTwoCupGoodShiftMap X C b) n := by
  obtain ⟨v,hv⟩ := (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_iff_exists_succ
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) 1 a b).mp hab
  exact (relativeTwoCupGoodShiftHomotopy X C v a b hv).homologyMap_eq n

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions
