import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockwiseEnumeration
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearch
import OAI.Algorithms.SubexponentialSAT.Subexp.SubspaceDimension
import OAI.Algorithms.SubexponentialSAT.Subexp.ElementaryMatrix
import OAI.Algorithms.SubexponentialSAT.Subexp.FiberEnumeration
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientSearch

namespace OAI.Algorithms

/-!
# Explicit local enumeration from the head-color partition

Each head-color side is searched independently for a kernel basis and a
complement. Their coefficient coordinates are combined using explicit finite
radix encodings. No basis of the ambient instance is chosen or searched for.
-/

namespace SubexponentialSAT.Subexp.LocalEnumeration

open scoped BigOperators
open SubexponentialSAT.Subexp.BlockwiseEnumeration

section Partition

variable {K U : Type*} {r : ℕ}

abbrev ColorFiber (color : U → Fin r) (g : Fin r) := {u : U // color u = g}

/-- Restrict to the color fibers; reconstruction reads the unique head color.
Both directions are explicit function evaluation. -/
def partitionEquiv (color : U → Fin r) :
    (U → K) ≃ ((g : Fin r) → ColorFiber color g → K) where
  toFun x _ u := x u.val
  invFun x u := x (color u) ⟨u, rfl⟩
  left_inv _ := rfl
  right_inv x := by
    funext g u
    rcases u with ⟨u, hu⟩
    cases hu
    rfl

/-- Separate the two coordinates of every local pair. -/
def piProductEquiv {G : Type*} (A B : G → Type*) :
    ((g : G) → A g × B g) ≃ ((g : G) → A g) × ((g : G) → B g) where
  toFun x := (fun g => (x g).1, fun g => (x g).2)
  invFun x g := (x.1 g, x.2 g)
  left_inv _ := rfl
  right_inv _ := rfl

variable [Semiring K]

/-- Enumerated kernel and complement coordinates for one color side. The
kernel vectors already live in the actual ambient subspace. -/
structure SideData (color : U → Fin r) (g : Fin r)
    (W : Submodule K (U → K)) where
  outerCount : ℕ
  innerCount : ℕ
  outerBase : Fin outerCount → ColorFiber color g → K
  incrementEquiv : Fin innerCount ≃ W
  assignmentEquiv : (ColorFiber color g → K) ≃ (Fin outerCount × Fin innerCount)
  reconstruction : ∀ o x u, assignmentEquiv.symm (o, x) u =
    outerBase o u + (incrementEquiv x).val u.val

variable [Fintype U]

/-- Combine independently enumerated sides into one universal-block
enumeration, with one joint outer index and one inner index per color. -/
def ofSides (color : U → Fin r) (W : Fin r → Submodule K (U → K))
    (hW : ∀ g z, z ∈ W g → ∀ u, color u ≠ g → z u = 0)
    (D : ∀ g, SideData color g (W g)) : LocalData K U r W where
  outerCount := ∏ g, (D g).outerCount
  innerCount g := (D g).innerCount
  outerBase o u := (D (color u)).outerBase (finPiFinEquiv.symm o (color u)) ⟨u, rfl⟩
  incrementEquiv g := (D g).incrementEquiv
  assignmentEquiv := (partitionEquiv color).trans
    ((Equiv.piCongrRight fun g => (D g).assignmentEquiv).trans
      ((piProductEquiv (fun g => Fin (D g).outerCount)
        (fun g => Fin (D g).innerCount)).trans
          (Equiv.prodCongr finPiFinEquiv (Equiv.refl _))))
  reconstruction o x := by
    funext u
    change (D (color u)).assignmentEquiv.symm
        (finPiFinEquiv.symm o (color u), x (color u)) ⟨u, rfl⟩ =
      (D (color u)).outerBase (finPiFinEquiv.symm o (color u)) ⟨u, rfl⟩ +
        (∑ g, ((D g).incrementEquiv (x g)).val) u
    rw [(D (color u)).reconstruction]
    simp only [Finset.sum_apply]
    congr 1
    symm
    apply Finset.sum_eq_single (color u)
    · intro g _ hg
      exact hW g _ ((D g).incrementEquiv (x g)).property u (Ne.symm hg)
    · simp

end Partition

section LocalSearch

open BlockSearch

variable {p r : ℕ} [Fact p.Prime]
variable {U : Type*} [Fintype U]

/-- A searched basis/complement pair on one side, with its actual kernel
identification, gives explicit finite coefficient indices for that side. -/
def sideDataOfPair (color : U → Fin r) (g : Fin r)
    (W : Submodule (ZMod p) (U → ZMod p))
    {m n : ℕ} (colE : Fin n ≃ ColorFiber color g)
    (A : Fin m → Fin n → ZMod p)
    (alphabet : List (ZMod p)) (hc : ∀ a, a ∈ alphabet)
    (c : Candidate (ZMod p) n × Candidate (ZMod p) n) (hg : GoodPair A c)
    (kerE : LinearMap.ker (matrixMap A) ≃ W)
    (hkerE : ∀ z u, (kerE z).val u.val = z.val (colE.symm u)) :
    SideData color g W where
  outerCount := p ^ c.2.1.val
  innerCount := p ^ c.1.1.val
  outerBase o u := combine c.2 ((zmodVectorEquiv p c.2.1.val).symm o) (colE.symm u)
  incrementEquiv := ((zmodVectorEquiv p c.1.1.val).symm.trans
    (kernelCoeffsEquiv alphabet hc c hg)).trans kerE
  assignmentEquiv := (reindexFunction colE).trans
    ((pairEquiv alphabet hc c hg).trans
      ((Equiv.prodCongr (zmodVectorEquiv p c.1.1.val)
        (zmodVectorEquiv p c.2.1.val)).trans (Equiv.prodComm _ _)))
  reconstruction o x u := by
    change combine c.1 ((zmodVectorEquiv p c.1.1.val).symm x) (colE.symm u) +
        combine c.2 ((zmodVectorEquiv p c.2.1.val).symm o) (colE.symm u) =
      combine c.2 ((zmodVectorEquiv p c.2.1.val).symm o) (colE.symm u) +
        (kerE (kernelCoeffsEquiv alphabet hc c hg
          ((zmodVectorEquiv p c.1.1.val).symm x))).val u.val
    rw [hkerE]
    exact add_comm _ _

/-- Run the actual finite search before constructing one side's coordinate
data. The kernel equivalence is structural input, not a basis oracle. -/
def sideDataOfMatrix (color : U → Fin r) (g : Fin r)
    (W : Submodule (ZMod p) (U → ZMod p))
    {m n : ℕ} (colE : Fin n ≃ ColorFiber color g)
    (A : Fin m → Fin n → ZMod p)
    (alphabet : List (ZMod p)) (hc : ∀ a, a ∈ alphabet)
    (kerE : LinearMap.ker (matrixMap A) ≃ W)
    (hkerE : ∀ z u, (kerE z).val u.val = z.val (colE.symm u)) :
    SideData color g W :=
  sideDataOfPair color g W colE A alphabet hc (findPair alphabet hc A)
    (findPair_good alphabet hc A) kerE hkerE

end LocalSearch

section ConstraintKernel

open BlockSearch
open _root_.OAI.Algorithms.SubexponentialSAT.Subexp.SubspaceDimension

variable {K U : Type*} [Field K] [DecidableEq K] [Fintype U]
variable {Δ m n : ℕ}
variable (S : Set U) (J : Fin Δ → Set U) (hJ : ∀ i, J i ⊆ S)
variable [Fintype S] [∀ i, Fintype (J i)] [DecidablePred (fun u => u ∈ S)]
variable (M : (i : Fin Δ) → (J i → K) →ₗ[K] (J i → K))

/-- The searched rectangular matrix and the encoded constraint map have the
same kernel. This equivalence changes only the membership proof. -/
def matrixConstraintKernelEquiv
    (rowE : Fin m ≃ ((i : Fin Δ) × J i)) (colE : Fin n ≃ S) :
    LinearMap.ker (matrixMap (encodedConstraintMatrix S J hJ M rowE colE)) ≃
      LinearMap.ker (encodedSideConstraintMap S J hJ M rowE colE) where
  toFun x := ⟨x.val, by
    funext a
    rw [← encodedConstraintMatrix_apply]
    exact congrFun x.property a⟩
  invFun x := ⟨x.val, by
    funext a
    change (∑ b, encodedConstraintMatrix S J hJ M rowE colE a b * x.val b) = 0
    rw [encodedConstraintMatrix_apply]
    exact congrFun x.property a⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Explicit zero extension identifies the searched side kernel with the
actual supported fixed space in the universal block. -/
noncomputable def supportedKernelEquiv
    (rowE : Fin m ≃ ((i : Fin Δ) × J i)) (colE : Fin n ≃ S) :
    LinearMap.ker (matrixMap (encodedConstraintMatrix S J hJ M rowE colE)) ≃
      SubexponentialSAT.SubspaceDimension.supportedFixedSpace S J hJ M :=
  (matrixConstraintKernelEquiv S J hJ M rowE colE).trans
    (encodedKernelEquiv S J hJ M rowE colE).toEquiv

omit [DecidableEq K] [Fintype U] [Fintype S] [∀ i, Fintype (J i)] in
@[simp] theorem supportedKernelEquiv_apply
    (rowE : Fin m ≃ ((i : Fin Δ) × J i)) (colE : Fin n ≃ S)
    (x : LinearMap.ker (matrixMap (encodedConstraintMatrix S J hJ M rowE colE)))
    (u : S) :
    (supportedKernelEquiv S J hJ M rowE colE x).val u.val = x.val (colE.symm u) := by
  simp [supportedKernelEquiv, matrixConstraintKernelEquiv, encodedKernelEquiv,
    decidableExtendByZero, u.property]

/-- Executable presentation of the supported space; the original mathematical
space is used only in the equality proof below. -/
def computedSupportedSpace : Submodule K (U → K) :=
  (SubexponentialSAT.SubspaceDimension.coordinateFixedSpace S J hJ M).map (decidableExtendByZero S)

omit [DecidableEq K] [Fintype U] [Fintype S] [∀ i, Fintype (J i)] in
theorem computedSupportedSpace_eq : computedSupportedSpace S J hJ M =
    SubexponentialSAT.SubspaceDimension.supportedFixedSpace S J hJ M := by
  unfold computedSupportedSpace SubexponentialSAT.SubspaceDimension.supportedFixedSpace
  rw [decidableExtendByZero_eq]

omit [DecidableEq K] [Fintype U] in
theorem coe_cast_submodule {P Q : Submodule K (U → K)} (h : P = Q) (x : P) :
    (cast (congrArg (fun R : Submodule K (U → K) => ↥R) h) x).val = x.val := by
  cases h
  rfl

/-- Transporting the kernel identification changes only a proof, while the
runtime space argument is the executable presentation. -/
noncomputable def computedKernelEquiv
    (rowE : Fin m ≃ ((i : Fin Δ) × J i)) (colE : Fin n ≃ S) :
    LinearMap.ker (matrixMap (encodedConstraintMatrix S J hJ M rowE colE)) ≃
      computedSupportedSpace S J hJ M :=
  (supportedKernelEquiv S J hJ M rowE colE).trans
    (Equiv.cast (congrArg (fun R : Submodule K (U → K) => ↥R)
      (computedSupportedSpace_eq S J hJ M).symm))

omit [DecidableEq K] [Fintype U] [Fintype S] [∀ i, Fintype (J i)] in
@[simp] theorem computedKernelEquiv_apply
    (rowE : Fin m ≃ ((i : Fin Δ) × J i)) (colE : Fin n ≃ S)
    (x : LinearMap.ker (matrixMap (encodedConstraintMatrix S J hJ M rowE colE)))
    (u : S) :
    (computedKernelEquiv S J hJ M rowE colE x).val u.val = x.val (colE.symm u) := by
  exact (congrFun (coe_cast_submodule (computedSupportedSpace_eq S J hJ M).symm
    (supportedKernelEquiv S J hJ M rowE colE x)) u.val).trans
      (supportedKernelEquiv_apply S J hJ M rowE colE x u)

end ConstraintKernel

section ActualLocalData

open BlockSearch
open _root_.OAI.Algorithms.SubexponentialSAT.Subexp.SubspaceDimension
open SubexponentialSAT.MulticolorTypes

variable {p r : ℕ} [Fact p.Prime]
variable {U : Type*} [Fintype U]
variable {Δ m n : ℕ}

/-- Each side's actual slot constraints determine its searched basis and
complement. No kernel or basis identification remains as a caller hypothesis. -/
noncomputable def computedSideDataOfConstraints (color : U → Fin r) (g : Fin r)
    (J : Fin Δ → Set U) (hJ : ∀ i, J i ⊆ {u | color u = g})
    [∀ i, Fintype (J i)]
    (M : (i : Fin Δ) → (J i → ZMod p) →ₗ[ZMod p] (J i → ZMod p))
    (rowE : Fin m ≃ ((i : Fin Δ) × J i)) (colE : Fin n ≃ ColorFiber color g)
    (alphabet : List (ZMod p)) (hc : ∀ a, a ∈ alphabet) :
    SideData color g (computedSupportedSpace {u | color u = g} J hJ M) :=
  sideDataOfMatrix color g _ colE
    (encodedConstraintMatrix {u | color u = g} J hJ M rowE colE) alphabet hc
    (computedKernelEquiv {u | color u = g} J hJ M rowE colE)
    (computedKernelEquiv_apply {u | color u = g} J hJ M rowE colE)

/-- The computed side data expressed with the original mathematical subspace.
The cast is a proof-only transport and performs no runtime submodule search. -/
noncomputable def sideDataOfConstraints (color : U → Fin r) (g : Fin r)
    (J : Fin Δ → Set U) (hJ : ∀ i, J i ⊆ {u | color u = g})
    [∀ i, Fintype (J i)]
    (M : (i : Fin Δ) → (J i → ZMod p) →ₗ[ZMod p] (J i → ZMod p))
    (rowE : Fin m ≃ ((i : Fin Δ) × J i)) (colE : Fin n ≃ ColorFiber color g)
    (alphabet : List (ZMod p)) (hc : ∀ a, a ∈ alphabet) :
    SideData color g (SubexponentialSAT.SubspaceDimension.supportedFixedSpace
      {u | color u = g} J hJ M) :=
  cast (congrArg (fun W => SideData color g W)
    (computedSupportedSpace_eq {u | color u = g} J hJ M))
    (computedSideDataOfConstraints color g J hJ M rowE colE alphabet hc)

variable {Q : ℕ}

/-- An explicit local enumeration for the actual multicolor fixed spaces.
Only local row/column enumerations and the finite field alphabet are supplied;
all basis and complement data are obtained by finite search on each side. -/
noncomputable def universalLocalData (t : Fin Q)
    (M : (g : Fin r) → (i : Fin Δ) →
      (Joint t g i → ZMod p) →ₗ[ZMod p] (Joint t g i → ZMod p))
    (rowSize colSize : Fin r → ℕ)
    (rowE : ∀ g, Fin (rowSize g) ≃ ((i : Fin Δ) × Joint t g i))
    (colE : ∀ g, Fin (colSize g) ≃ Side (Δ := Δ) t g)
    (alphabet : List (ZMod p)) (hc : ∀ a, a ∈ alphabet) :
    LocalData (ZMod p) (UniversalType r Q Δ) r
      (fun g => universalFixedSpace t g (M g)) := by
  let color : UniversalType r Q Δ → Fin r := fun u => u.head t
  let W := fun g => computedSupportedSpace (side t g) (joint t g)
    (joint_subset_side t g) (M g)
  have hW : W = fun g => universalFixedSpace t g (M g) := by
    funext g
    exact computedSupportedSpace_eq (side t g) (joint t g) (joint_subset_side t g) (M g)
  have hs : ∀ g z, z ∈ W g → ∀ u, color u ≠ g → z u = 0 := by
    intro g z hz u hu
    rw [hW] at hz
    exact universalFixedSpace_supported t g (M g) hz u hu
  let D : LocalData (ZMod p) (UniversalType r Q Δ) r W :=
    ofSides color W hs (fun g => computedSideDataOfConstraints color g (joint t g)
      (joint_subset_side t g) (M g) (rowE g) (colE g) alphabet hc)
  exact cast (congrArg (fun H => LocalData (ZMod p) (UniversalType r Q Δ) r H) hW) D

/-- The local enumeration uses the executable elementary-matrix recurrence
and yields data for the exact matrices in the layout's rank/support proofs. -/
noncomputable def universalLocalDataOfCoefficients (t : Fin Q) (R : ℕ) (c : ℕ → ZMod p)
    (rowSize colSize : Fin r → ℕ)
    (rowE : ∀ g, Fin (rowSize g) ≃ ((i : Fin Δ) × Joint t g i))
    (colE : ∀ g, Fin (colSize g) ≃ Side (Δ := Δ) t g)
    (alphabet : List (ZMod p)) (hc : ∀ a, a ∈ alphabet) :
    LocalData (ZMod p) (UniversalType r Q Δ) r
      (fun g => universalFixedSpace t g
        (fun i => (MatrixSupport.jointMatrix i t g R c).mulVecLin)) := by
  let M : (g : Fin r) → (i : Fin Δ) →
      (Joint t g i → ZMod p) →ₗ[ZMod p] (Joint t g i → ZMod p) := fun g i =>
    (ElementaryMatrix.jointMatrixDP i t g R c).mulVecLin
  let D : LocalData (ZMod p) (UniversalType r Q Δ) r
      (fun g => universalFixedSpace t g (M g)) :=
    universalLocalData t M rowSize colSize rowE colE alphabet hc
  have hM : M = fun g i => (MatrixSupport.jointMatrix i t g R c).mulVecLin := by
    funext g i
    exact congrArg Matrix.mulVecLin (ElementaryMatrix.jointMatrixDP_eq i t g R c)
  exact cast (congrArg (fun H : (g : Fin r) → (i : Fin Δ) →
      (Joint t g i → ZMod p) →ₗ[ZMod p] (Joint t g i → ZMod p) =>
    LocalData (ZMod p) (UniversalType r Q Δ) r
    (fun g => universalFixedSpace t g (H g))) hM) D

/-- Canonical finite lists discharge every enumeration input of the local
constructor. All basis and complement coordinates still come from the actual
finite search, over the exact supplied matrix coefficients. -/
noncomputable def canonicalLocalData (t : Fin Q) (R : ℕ) (c : ℕ → ZMod p) :
    LocalData (ZMod p) (UniversalType r Q Δ) r
      (fun g => universalFixedSpace t g
        (fun i => (MatrixSupport.jointMatrix i t g R c).mulVecLin)) :=
  universalLocalDataOfCoefficients t R c
    (fun g => (FiberEnumeration.rowList (Δ := Δ) t g).length)
    (fun g => (FiberEnumeration.sideList (Δ := Δ) t g).length)
    (fun g => FiberEnumeration.rowEquiv (Δ := Δ) t g)
    (fun g => FiberEnumeration.sideEquiv (Δ := Δ) t g)
    (CoefficientSearch.alphabet p)
    (CoefficientSearch.mem_alphabet p (Fact.out : p.Prime).pos)

/-- The exact finite rectangular matrix searched on one head-color side.
Rows are slot/joint-coordinate pairs; columns are side coordinates. -/
def canonicalConstraintMatrix (t : Fin Q) (g : Fin r) (R : ℕ) (c : ℕ → ZMod p) :
    Fin (FiberEnumeration.rowList (Δ := Δ) t g).length →
      Fin (FiberEnumeration.sideList (Δ := Δ) t g).length → ZMod p :=
  encodedConstraintMatrix (side t g) (joint t g) (joint_subset_side t g)
    (fun i => (ElementaryMatrix.jointMatrixDP i t g R c).mulVecLin)
    (FiberEnumeration.rowEquiv (Δ := Δ) t g)
    (FiberEnumeration.sideEquiv (Δ := Δ) t g)

/-- Canonical row-major serialization of the selected constraint matrix. -/
def selectedConstraintEntries (t : Fin Q) (g : Fin r) (A R : ℕ) : List (ZMod p) :=
  (List.ofFn fun a : Fin (FiberEnumeration.rowList (Δ := Δ) t g).length =>
    List.ofFn fun b : Fin (FiberEnumeration.sideList (Δ := Δ) t g).length =>
      canonicalConstraintMatrix (Δ := Δ) t g R
        (CoefficientSearch.coefficientsNat p A R) a b).flatten

@[simp] theorem selectedConstraintEntries_length (t : Fin Q) (g : Fin r) (A R : ℕ) :
    (selectedConstraintEntries (p := p) (Δ := Δ) t g A R).length =
      (FiberEnumeration.rowList (Δ := Δ) t g).length *
        (FiberEnumeration.sideList (Δ := Δ) t g).length := by
  simp [selectedConstraintEntries, List.length_flatten, List.map_ofFn, Function.comp_def]

/-- The actual local basis/complement tuple, exposed for encoded search and
table-copy programs. It searches exactly the canonical constraint matrix. -/
def selectedPair (t : Fin Q) (g : Fin r) (A R : ℕ) :
    Candidate (ZMod p) (FiberEnumeration.sideList (Δ := Δ) t g).length ×
      Candidate (ZMod p) (FiberEnumeration.sideList (Δ := Δ) t g).length :=
  findPair (CoefficientSearch.alphabet p)
    (CoefficientSearch.mem_alphabet p (Fact.out : p.Prime).pos)
    (canonicalConstraintMatrix t g R (CoefficientSearch.coefficientsNat p A R))

theorem selectedPair_good (t : Fin Q) (g : Fin r) (A R : ℕ) :
    GoodPair (canonicalConstraintMatrix (Δ := Δ) t g R
      (CoefficientSearch.coefficientsNat p A R)) (selectedPair t g A R) :=
  findPair_good _ _ _

/-- Any actual finite search may supply its successful side pairs. Only their
checked `GoodPair` specifications are used; no equality with a different
search order or previously selected basis is required. -/
noncomputable def universalLocalDataForPairs (t : Fin Q) (R : ℕ) (coeff : ℕ → ZMod p)
    (pairs : (g : Fin r) →
      Candidate (ZMod p) (FiberEnumeration.sideList (Δ := Δ) t g).length ×
        Candidate (ZMod p) (FiberEnumeration.sideList (Δ := Δ) t g).length)
    (hpairs : ∀ g, GoodPair (canonicalConstraintMatrix (Δ := Δ) t g R coeff) (pairs g)) :
    LocalData (ZMod p) (UniversalType r Q Δ) r
      (fun g => universalFixedSpace t g
        (fun i => (MatrixSupport.jointMatrix i t g R coeff).mulVecLin)) := by
  let M : (g : Fin r) → (i : Fin Δ) →
      (Joint t g i → ZMod p) →ₗ[ZMod p] (Joint t g i → ZMod p) := fun g i =>
    (ElementaryMatrix.jointMatrixDP i t g R coeff).mulVecLin
  let W := fun g => computedSupportedSpace (side t g) (joint t g)
    (joint_subset_side t g) (M g)
  have hW : W = fun g => universalFixedSpace t g
      (fun i => (MatrixSupport.jointMatrix i t g R coeff).mulVecLin) := by
    funext g
    rw [show W g = SubexponentialSAT.SubspaceDimension.supportedFixedSpace (side t g) (joint t g)
        (joint_subset_side t g) (M g) from
      computedSupportedSpace_eq (side t g) (joint t g) (joint_subset_side t g) (M g)]
    apply congrArg (fun H => universalFixedSpace t g H)
    funext i
    exact congrArg Matrix.mulVecLin (ElementaryMatrix.jointMatrixDP_eq i t g R coeff)
  have hs : ∀ g z, z ∈ W g → ∀ u, u.head t ≠ g → z u = 0 := by
    intro g z hz u hu
    rw [hW] at hz
    exact universalFixedSpace_supported t g _ hz u hu
  let D : LocalData (ZMod p) (UniversalType r Q Δ) r W :=
    ofSides (fun u : UniversalType r Q Δ => u.head t) W hs (fun g =>
      sideDataOfPair (fun u : UniversalType r Q Δ => u.head t) g (W g)
        (FiberEnumeration.sideEquiv (Δ := Δ) t g)
        (canonicalConstraintMatrix (Δ := Δ) t g R coeff)
        (CoefficientSearch.alphabet p)
        (CoefficientSearch.mem_alphabet p (Fact.out : p.Prime).pos)
        (pairs g) (hpairs g)
        (computedKernelEquiv (side t g) (joint t g) (joint_subset_side t g) (M g)
          (FiberEnumeration.rowEquiv (Δ := Δ) t g) (FiberEnumeration.sideEquiv (Δ := Δ) t g))
        (computedKernelEquiv_apply (side t g) (joint t g) (joint_subset_side t g) (M g)
          (FiberEnumeration.rowEquiv (Δ := Δ) t g) (FiberEnumeration.sideEquiv (Δ := Δ) t g)))
  exact cast (congrArg (fun H => LocalData (ZMod p) (UniversalType r Q Δ) r H) hW) D

/-- Fully selected local data: coefficient search, matrix recurrence,
constraint encoding, basis/complement search, and mixed-radix enumeration. -/
noncomputable def selectedLocalData (t : Fin Q) (A R : ℕ) :
    LocalData (ZMod p) (UniversalType r Q Δ) r
      (fun g => universalFixedSpace t g
        (fun i => (MatrixSupport.jointMatrix i t g R
          (CoefficientSearch.coefficientsNat p A R)).mulVecLin)) :=
  canonicalLocalData t R (CoefficientSearch.coefficientsNat p A R)

end ActualLocalData

end SubexponentialSAT.Subexp.LocalEnumeration

end OAI.Algorithms
