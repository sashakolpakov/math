import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpWeightCode
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutSpec
import OAI.Algorithms.SubexponentialSAT.SubexpKernelCorrectness

namespace OAI.Algorithms

/-!
# Computed weights for reconstructed r-group inputs

Field addition happens before the arbitrary coordinate lift.  Disjoint
supports prove that a reconstructed input equals the base outside all color
supports and equals base plus the own-color increment on each color support.
These facts discharge the exact monomial split used by the executable kernel.
-/

namespace SubexponentialSAT.SubexpComputedWeights

open scoped BigOperators

/-- Enumerate the complement of the supplied color supports. -/
def outsideCoordinates {D r : ℕ} (groups : Fin r → List (Fin D)) : List (Fin D) :=
  (List.finRange D).filter fun i =>
    decide (i ∉ Finset.univ.biUnion (fun g => (groups g).toFinset))

theorem outsideCoordinates_nodup {D r : ℕ} (groups : Fin r → List (Fin D)) :
    (outsideCoordinates groups).Nodup :=
  (List.nodup_finRange D).filter _

@[simp] theorem outsideCoordinates_toFinset {D r : ℕ}
    (groups : Fin r → List (Fin D)) :
    (outsideCoordinates groups).toFinset =
      (Finset.univ.biUnion (fun g => (groups g).toFinset))ᶜ := by
  ext i
  simp [outsideCoordinates]

section Reconstruction

variable {D r : ℕ} {F : Type*} [AddCommMonoid F]

/-- Reconstruct the full field assignment before applying any coordinate lift. -/
def reconstruct (base : Fin D → F) (delta : Fin r → Fin D → F) : Fin D → F :=
  base + ∑ g, delta g

theorem reconstruct_on_color (groups : Fin r → List (Fin D))
    (hdisjoint : Pairwise (fun g h =>
      Disjoint (groups g).toFinset (groups h).toFinset))
    (base : Fin D → F) (delta : Fin r → Fin D → F)
    (hsupported : ∀ g i, i ∉ (groups g).toFinset → delta g i = 0)
    (g : Fin r) (i : Fin D) (hi : i ∈ (groups g).toFinset) :
    reconstruct base delta i = base i + delta g i := by
  simp only [reconstruct, Pi.add_apply, Finset.sum_apply]
  congr 1
  apply Finset.sum_eq_single g
  · intro h hh hne
    apply hsupported h i
    intro hih
    exact Finset.disjoint_left.mp (hdisjoint hne) hih hi
  · simp

theorem reconstruct_outside (groups : Fin r → List (Fin D))
    (base : Fin D → F) (delta : Fin r → Fin D → F)
    (hsupported : ∀ g i, i ∉ (groups g).toFinset → delta g i = 0)
    (i : Fin D) (hi : i ∈ outsideCoordinates groups) :
    reconstruct base delta i = base i := by
  have hout : i ∉ Finset.univ.biUnion (fun g => (groups g).toFinset) := by
    simpa only [outsideCoordinates_toFinset, Finset.mem_compl] using
      (List.mem_toFinset.mpr hi)
  have hz : ∑ g, delta g i = 0 := by
    apply Finset.sum_eq_zero
    intro g hg
    apply hsupported g i
    intro hig
    exact hout (Finset.mem_biUnion.mpr ⟨g, hg, hig⟩)
  simp only [reconstruct, Pi.add_apply, Finset.sum_apply, hz, add_zero]

end Reconstruction

section Values

variable {D r : ℕ} {F R : Type*} [AddCommMonoid F] [CommSemiring R]

def outsideValue (groups : Fin r → List (Fin D)) (lift : F → R)
    (base : Fin D → F) (a : Fin D → ℕ) : R :=
  (SubexpWeightCode.weightWithCost (fun i => lift (base i)) a
    (outsideCoordinates groups)).1

def insideValue (groups : Fin r → List (Fin D)) (lift : F → R)
    (base delta : Fin D → F) (a : Fin D → ℕ) (g : Fin r) : R :=
  (SubexpWeightCode.weightWithCost (fun i => lift (base i + delta i)) a (groups g)).1

def outsideCode (groups : Fin r → List (Fin D)) (lift : F → R)
    (base : Fin D → F) (a : Fin D → ℕ) : SymbolicCost.CoeffList D R :=
  (SubexpWeightCode.rawWeightWithCost (fun i => lift (base i)) a
    (outsideCoordinates groups)).1

def insideCode (groups : Fin r → List (Fin D)) (lift : F → R)
    (base delta : Fin D → F) (a : Fin D → ℕ) (g : Fin r) :
    SymbolicCost.CoeffList D R :=
  (SubexpWeightCode.rawWeightWithCost (fun i => lift (base i + delta i)) a (groups g)).1

omit [AddCommMonoid F] in
theorem outsideCode_denote (groups : Fin r → List (Fin D)) (lift : F → R)
    (base : Fin D → F) (a : Fin D → ℕ) :
    SymbolicCost.denote (outsideCode groups lift base a) =
      WeightedSupport.scalarHom (outsideValue groups lift base a) :=
  SubexpWeightCode.rawWeightWithCost_denote _ _ _

theorem insideCode_denote (groups : Fin r → List (Fin D)) (lift : F → R)
    (base delta : Fin D → F) (a : Fin D → ℕ) (g : Fin r) :
    SymbolicCost.denote (insideCode groups lift base delta a g) =
      WeightedSupport.scalarHom (insideValue groups lift base delta a g) :=
  SubexpWeightCode.rawWeightWithCost_denote _ _ _

theorem weightWithCost_congr (x y : Fin D → R) (a : Fin D → ℕ)
    (support : List (Fin D)) (hxy : ∀ i ∈ support, x i = y i) :
    (SubexpWeightCode.weightWithCost x a support).1 =
      (SubexpWeightCode.weightWithCost y a support).1 := by
  simp only [SubexpWeightCode.weightWithCost_value]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [hxy i hi]

/-- Exact splitting of computed weights, derived from support and field
reconstruction.  The coordinate lift is an arbitrary function. -/
theorem momentWeight_reconstruct (groups : Fin r → List (Fin D))
    (hnodup : ∀ g, (groups g).Nodup)
    (hdisjoint : Pairwise (fun g h =>
      Disjoint (groups g).toFinset (groups h).toFinset))
    (lift : F → R) (base : Fin D → F) (delta : Fin r → Fin D → F)
    (hsupported : ∀ g i, i ∉ (groups g).toFinset → delta g i = 0)
    (a : Fin D →₀ ℕ) :
    Moments.weight a (fun i => lift (reconstruct base delta i)) =
      outsideValue groups lift base a * ∏ g, insideValue groups lift base (delta g) a g := by
  rw [SubexpWeightCode.momentWeight_eq_computed_partition groups
    (outsideCoordinates groups) hnodup (outsideCoordinates_nodup groups)
    hdisjoint (outsideCoordinates_toFinset groups)]
  apply congrArg₂ (· * ·)
  · apply weightWithCost_congr
    intro i hi
    rw [reconstruct_outside groups base delta hsupported i hi]
  · apply Finset.prod_congr rfl
    intro g hg
    apply weightWithCost_congr
    intro i hi
    rw [reconstruct_on_color groups hdisjoint base delta hsupported g i
      (List.mem_toFinset.mpr hi)]

end Values

section Enumeration

open SubexpLayoutSpec

variable {D p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {F E R : Type*} [Fintype F] [Field E] [Algebra (ZMod p) E] [CommSemiring R]
  {P : Factor.Pattern (Fin D) F} {c : Parameters p k Δ r tau}
  {L : Layout (E := E) P c} {t : Fin c.Q}

/-- Convert the explicit enumeration's product target to the dependent-fiber
form consumed by the executable kernel correctness theorem. -/
def enumerationFiberEquiv (data : EnumerationData L t) :
    (Fin D → ZMod p) ≃ Σ _ : Fin data.outerCount, ∀ g, Fin (data.innerCount g) :=
  data.assignmentEquiv.trans (Equiv.sigmaEquivProd _ _).symm

@[simp] theorem enumerationFiberEquiv_symm (data : EnumerationData L t)
    (o : Fin data.outerCount) (x : ∀ g, Fin (data.innerCount g)) :
    (enumerationFiberEquiv data).symm ⟨o, x⟩ = data.assignmentEquiv.symm (o, x) := rfl

/-- Exact computed weight factorization for the explicit layout enumeration.
Increment support is discharged from layout membership, not assumed as a
global factorization property. -/
theorem enumeration_weight_split (data : EnumerationData L t)
    (groups : Fin r → List (Fin D)) (hnodup : ∀ g, (groups g).Nodup)
    (hsupport : ∀ g, (groups g).toFinset = L.support t g)
    (lift : ZMod p → R) (a : Fin D →₀ ℕ)
    (o : Fin data.outerCount) (x : ∀ g, Fin (data.innerCount g)) :
    Moments.weight a (fun i => lift (data.assignmentEquiv.symm (o, x) i)) =
      outsideValue groups lift (data.outerBase o) a *
        ∏ g, insideValue groups lift (data.outerBase o) (data.increment g (x g)) a g := by
  rw [data.reconstruct_eq]
  apply momentWeight_reconstruct groups hnodup
  · simpa only [hsupport] using L.support_disjoint t
  · intro g i hi
    exact L.supported t g _ (data.increment_mem g (x g)) i
      (by simpa only [hsupport] using hi)

/-- This is precisely the `hw` premise of the r-group kernel bridge, with
the weights computed on a base point and one own-color increment. -/
theorem enumeration_kernel_weight_split (data : EnumerationData L t)
    (groups : Fin r → List (Fin D)) (hnodup : ∀ g, (groups g).Nodup)
    (hsupport : ∀ g, (groups g).toFinset = L.support t g)
    (lift : ZMod p → R) (a : Fin D →₀ ℕ)
    (o : Fin data.outerCount) (x : ∀ g, Fin (data.innerCount g)) :
    Moments.weight a
        (fun i => lift ((enumerationFiberEquiv data).symm ⟨o, x⟩ i)) =
      outsideValue groups lift (data.outerBase o) a *
        ∏ g, insideValue groups lift (data.outerBase o) (data.increment g (x g)) a g :=
  enumeration_weight_split data groups hnodup hsupport lift a o x

/-- The raw outside scalar code discharges the kernel's local `hC` premise. -/
theorem enumeration_outsideCode_denote (data : EnumerationData L t)
    (groups : Fin r → List (Fin D)) (lift : ZMod p → R)
    (a : Fin D → ℕ) (o : Fin data.outerCount) :
    SymbolicCost.denote (outsideCode groups lift (data.outerBase o) a) =
      WeightedSupport.scalarHom
        (outsideValue groups lift (data.outerBase o) (Finsupp.equivFunOnFinite.symm a)) :=
  outsideCode_denote groups lift (data.outerBase o) a

/-- The raw one-color scalar code discharges the kernel's local `hW` premise. -/
theorem enumeration_insideCode_denote (data : EnumerationData L t)
    (groups : Fin r → List (Fin D)) (lift : ZMod p → R)
    (a : Fin D → ℕ) (o : Fin data.outerCount)
    (g : Fin r) (y : Fin (data.innerCount g)) :
    SymbolicCost.denote
        (insideCode groups lift (data.outerBase o) (data.increment g y) a g) =
      WeightedSupport.scalarHom
        (insideValue groups lift (data.outerBase o) (data.increment g y)
          (Finsupp.equivFunOnFinite.symm a) g) :=
  insideCode_denote groups lift (data.outerBase o) (data.increment g y) a g

/-- With zero representatives for the other colors, the local group input
is exactly the outer base plus its own increment. -/
theorem enumeration_single_color (data : EnumerationData L t)
    (o : Fin data.outerCount) (g : Fin r) (y : Fin (data.innerCount g)) :
    (enumerationFiberEquiv data).symm
        ⟨o, Function.update (fun h => data.zeroIndex h) g y⟩ =
      data.outerBase o + data.increment g y := by
  rw [enumerationFiberEquiv_symm, data.reconstruct_eq]
  congr 1
  rw [Finset.sum_eq_single g]
  · simp
  · intro h hh hne
    simp [Function.update, hne]
  · simp

/-- Actual outer/inner block lists with computed scalar weights.  The only
programs supplied externally here are the individual group expressions. -/
def computedBlocks (data : EnumerationData L t)
    (groups : Fin r → List (Fin D)) (lift : ZMod p → R)
    (code : (Fin D → ℕ) → ∀ _o : Fin data.outerCount, ∀ g : Fin r,
      Fin (data.innerCount g) → Algorithm.Expr (SymbolicCost.CoeffList D R))
    (a : Fin D → ℕ) :
    List (SubexpAlgorithm.Block (SymbolicCost.CoeffList D R)) :=
  SubexpKernelCorrectness.buildBlocks (List.finRange data.outerCount)
    (fun o => outsideCode groups lift (data.outerBase o) a)
    (fun _ g => List.finRange (data.innerCount g))
    (fun o g y => insideCode groups lift (data.outerBase o) (data.increment g y) a g)
    (code a)

/-- The kernel bridge with all scalar-code denotation, weight splitting,
and finite-list enumeration premises discharged.  Only the supplied group
expression semantics and its independently provable own-coordinate
invariance remain as local program premises. -/
theorem execute_computedBlocks_eq_separatedJet (data : EnumerationData L t)
    (groups : Fin r → List (Fin D)) (hnodup : ∀ g, (groups g).Nodup)
    (hsupport : ∀ g, (groups g).toFinset = L.support t g)
    (lift : ZMod p → R)
    (code : (Fin D → ℕ) → ∀ _o : Fin data.outerCount, ∀ g : Fin r,
      Fin (data.innerCount g) → Algorithm.Expr (SymbolicCost.CoeffList D R))
    (A : Fin r → (Fin D → ZMod p) → SymbolicCost.Poly D R)
    (hcode : ∀ a o g y, ((code a o g y).map SymbolicCost.denote).eval =
      A g (data.outerBase o + data.increment g y))
    (hA : ∀ o g x y, x g = y g →
      A g ((enumerationFiberEquiv data).symm ⟨o, x⟩) =
        A g ((enumerationFiberEquiv data).symm ⟨o, y⟩)) :
    SubexpAlgorithm.executeJet (computedBlocks data groups lift code) =
      (List.range D).map fun j =>
        (SubexpCounting.separatedJet (D + 1) D (enumerationFiberEquiv data)
          (fun _ g => data.zeroIndex g) A
          (fun a o => outsideValue groups lift (data.outerBase o) a)
          (fun a o g y => insideValue groups lift (data.outerBase o)
            (data.increment g y) a g)).coeff j := by
  apply SubexpKernelCorrectness.executeJet_buildBlocks_eq_separatedJet
    (enumerationFiberEquiv data) (fun _ g => data.zeroIndex g)
    (List.finRange data.outerCount) (List.nodup_finRange _) (by intro o; simp)
    (fun a o => outsideCode groups lift (data.outerBase o) a)
    (fun _ g => List.finRange (data.innerCount g))
    (by intro o g; exact List.nodup_finRange _) (by intro o g y; simp)
    (fun a o g y => insideCode groups lift (data.outerBase o) (data.increment g y) a g)
    code A (fun z i => lift (z i))
    (fun a o => outsideValue groups lift (data.outerBase o) a)
    (fun a o g y => insideValue groups lift (data.outerBase o) (data.increment g y) a g)
  · exact enumeration_outsideCode_denote data groups lift
  · exact enumeration_insideCode_denote data groups lift
  · intro a o g y
    rw [hcode, enumeration_single_color]
  · exact hA
  · exact enumeration_kernel_weight_split data groups hnodup hsupport lift

end Enumeration

end SubexponentialSAT.SubexpComputedWeights

end OAI.Algorithms
