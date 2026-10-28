import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Set.Finite.Lattice

/-! # Locally Finite Operation -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteOperation.Cycles.SpatialSupport

noncomputable section

section

/-!
# Finite simplex operations on spatially locally finite coefficients

A kernel assigns a finite linear combination of target indices to each source
index. If each target image lies in its source image, then the operation extends
to spatially locally finite coefficients. Nonempty target images make every
coefficient sum genuinely finite. Spatial local finiteness follows by taking a
finite union of the finite kernel supports over source images meeting a fixed
neighborhood.
-/

open Set Filter Function
open scoped _root_.Topology BigOperators

variable {X ι κ : Type*} [TopologicalSpace X]
variable {R : Type*} [Semiring R]

/-- The coefficient formula for a finite-kernel operation. -/
def kernelSum (K : ι → κ →₀ R) (c : ι → R) (j : κ) : R :=
  ∑ᶠ i, c i * K i j

/-- Nonzero output has a source with nonzero coefficient and nonzero kernel entry. -/
theorem exists_contributor_of_kernelSum_ne_zero (K : ι → κ →₀ R)
    (c : ι → R) (j : κ) (h : kernelSum K c j ≠ 0) :
    ∃ i, c i ≠ 0 ∧ K i j ≠ 0 := by
  by_contra! hn
  apply h
  apply finsum_eq_zero_of_forall_eq_zero
  intro i
  by_cases hi : c i = 0
  · simp [hi]
  · simp [hn i hi]

/-- Spatial local finiteness makes the set of possible contributors finite. -/
theorem finite_kernelContributors {imageA : ι → Set X} {imageB : κ → Set X}
    (K : ι → κ →₀ R)
    (himage : ∀ i j, j ∈ (K i).support → imageB j ⊆ imageA i)
    (hne : ∀ j, (imageB j).Nonempty) (c : LocallyFiniteChains.Cycles.SpatialSupport.module R imageA) (j : κ) :
    {i | c i ≠ 0 ∧ K i j ≠ 0}.Finite := by
  obtain ⟨x, hx⟩ := hne j
  have hc : LocallyFinite (fun i => {x | c i ≠ 0 ∧ x ∈ imageA i}) := c.property
  apply (hc.point_finite x).subset
  rintro i ⟨hci, hKi⟩
  exact ⟨hci, himage i j (Finsupp.mem_support_iff.mpr hKi) hx⟩

/-- Every coefficient sum defining the extension has finite support, even
over coefficient semirings with zero divisors. -/
theorem kernelTerm_hasFiniteSupport {imageA : ι → Set X} {imageB : κ → Set X}
    (K : ι → κ →₀ R)
    (himage : ∀ i j, j ∈ (K i).support → imageB j ⊆ imageA i)
    (hne : ∀ j, (imageB j).Nonempty) (c : LocallyFiniteChains.Cycles.SpatialSupport.module R imageA) (j : κ) :
    HasFiniteSupport (fun i => c i * K i j) := by
  apply (finite_kernelContributors K himage hne c j).subset
  intro i hi
  exact ⟨fun hci => hi (by simp [hci]), fun hKi => hi (by simp [hKi])⟩

/-- A spatially subordinate finite kernel preserves actual local finiteness. -/
theorem kernelSum_locallyFinite {imageA : ι → Set X} {imageB : κ → Set X}
    (K : ι → κ →₀ R)
    (himage : ∀ i j, j ∈ (K i).support → imageB j ⊆ imageA i)
    (c : LocallyFiniteChains.Cycles.SpatialSupport.module R imageA) : LocallyFiniteChains.Cycles.SpatialSupport.IsLocallyFinite imageB (kernelSum K c) := by
  intro x
  obtain ⟨U, hU, hfin⟩ := (show LocallyFiniteChains.Cycles.SpatialSupport.IsLocallyFinite imageA (c : ι → R) from c.property) x
  let I : Set ι := {i | ({y | c i ≠ 0 ∧ y ∈ imageA i} ∩ U).Nonempty}
  have hI : I.Finite := hfin
  have hJ : (⋃ i ∈ I, ((K i).support : Set κ)).Finite :=
    hI.biUnion (fun i _ => (K i).support.finite_toSet)
  refine ⟨U, hU, hJ.subset ?_⟩
  rintro j ⟨y, ⟨hj, hy⟩, hyU⟩
  obtain ⟨i, hci, hKi⟩ := exists_contributor_of_kernelSum_ne_zero K c j hj
  have hsupport : j ∈ (K i).support := Finsupp.mem_support_iff.mpr hKi
  have hi : i ∈ I := ⟨y, ⟨hci, himage i j hsupport hy⟩, hyU⟩
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hsupport⟩⟩

/-- The genuine extension of a finite simplex operation to spatially locally
finite coefficients. The containment and nonemptiness conditions are checked
geometric hypotheses, not an assumed Borel--Moore class. -/
def kernelOperation {imageA : ι → Set X} {imageB : κ → Set X}
    (K : ι → κ →₀ R)
    (himage : ∀ i j, j ∈ (K i).support → imageB j ⊆ imageA i)
    (hne : ∀ j, (imageB j).Nonempty) :
    LocallyFiniteChains.Cycles.SpatialSupport.module R imageA →ₗ[R] LocallyFiniteChains.Cycles.SpatialSupport.module R imageB where
  toFun c := ⟨kernelSum K c, kernelSum_locallyFinite K himage c⟩
  map_add' c d := by
    apply Subtype.ext
    funext j
    change (∑ᶠ i, (c i + d i) * K i j) =
      (∑ᶠ i, c i * K i j) + (∑ᶠ i, d i * K i j)
    simp_rw [add_mul]
    exact finsum_add_distrib (kernelTerm_hasFiniteSupport K himage hne c j)
      (kernelTerm_hasFiniteSupport K himage hne d j)
  map_smul' r c := by
    apply Subtype.ext
    funext j
    change (∑ᶠ i, (r * c i) * K i j) = r * (∑ᶠ i, c i * K i j)
    simp_rw [mul_assoc]
    exact (mul_finsum' (fun i => c i * K i j) r
      (kernelTerm_hasFiniteSupport K himage hne c j)).symm

@[simp]
theorem kernelOperation_apply {imageA : ι → Set X} {imageB : κ → Set X}
    (K : ι → κ →₀ R)
    (himage : ∀ i j, j ∈ (K i).support → imageB j ⊆ imageA i)
    (hne : ∀ j, (imageB j).Nonempty) (c : LocallyFiniteChains.Cycles.SpatialSupport.module R imageA) (j : κ) :
    kernelOperation K himage hne c j = ∑ᶠ i, c i * K i j := rfl

/-- On ordinary finite coefficients, the coefficient formula is the literal
finite sum over the original support. -/
theorem kernelSum_ofFinsupp (K : ι → κ →₀ R) (c : ι →₀ R) (j : κ) :
    kernelSum K c j = ∑ i ∈ c.support, c i * K i j := by
  classical
  apply finsum_eq_finsetSum_of_support_subset
  intro i hi
  exact Finsupp.mem_support_iff.mpr (fun hci => hi (by simp [hci]))

/-- The locally finite extension agrees with the ordinary finite linear
combination on every finitely supported input. -/
theorem kernelOperation_ofFinsupp {imageA : ι → Set X} {imageB : κ → Set X}
    (K : ι → κ →₀ R)
    (himage : ∀ i j, j ∈ (K i).support → imageB j ⊆ imageA i)
    (hne : ∀ j, (imageB j).Nonempty) (c : ι →₀ R) :
    kernelOperation K himage hne (LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp imageA c) =
      LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp imageB (Finsupp.linearCombination R K c) := by
  classical
  apply Subtype.ext
  funext j
  change kernelSum K c j = (∑ i ∈ c.support, c i • K i) j
  rw [kernelSum_ofFinsupp]
  simp

end

/-!
# Algebra of spatially subordinate finite-kernel operations

Every output coefficient can be computed from the finite set of source
simplices containing one point of its image. This finite reduction proves
composition, as well as the additive and identity laws, for the genuine
locally finite extensions.
-/

open Set Function
open scoped BigOperators

variable {X ι κ μ : Type*} [TopologicalSpace X]
variable {R : Type*} [Semiring R]

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Retain precisely the coefficients whose indexed images contain a point.
Spatial local finiteness proves that this is an ordinary finite chain. -/
def localCoefficients {image : ι → Set X} (c : LocallyFiniteChains.Cycles.SpatialSupport.module R image) (x : X) : ι →₀ R := by
  classical
  refine Finsupp.ofSupportFinite (fun i => if x ∈ image i then c i else 0) ?_
  have hc : LocallyFinite (fun i => {y | c i ≠ 0 ∧ y ∈ image i}) := c.property
  apply (hc.point_finite x).subset
  intro i hi
  by_cases hx : x ∈ image i
  · exact ⟨by simpa only [mem_support, ite_eq_left hx] using hi, hx⟩
  · simp only [mem_support, ite_eq_right hx, ne_eq, not_true_eq_false] at hi

@[simp]
theorem localCoefficients_apply {image : ι → Set X} (c : LocallyFiniteChains.Cycles.SpatialSupport.module R image) (x : X)
    (i : ι) : localCoefficients c x i = if x ∈ image i then c i else 0 := by
  classical
  rfl

omit [TopologicalSpace X] in
/-- A subordinate kernel is local at every point of a target image. -/
theorem kernelSum_congr_at {imageA : ι → Set X} {imageB : κ → Set X}
    (K : ι → κ →₀ R)
    (hK : ∀ i j, j ∈ (K i).support → imageB j ⊆ imageA i)
    {c d : ι → R} {x : X} (hcd : ∀ i, x ∈ imageA i → c i = d i)
    {j : κ} (hx : x ∈ imageB j) : kernelSum K c j = kernelSum K d j := by
  apply finsum_congr
  intro i
  by_cases hij : K i j = 0
  · simp only [hij, mul_zero]
  · rw [hcd i (hK i j (Finsupp.mem_support_iff.mpr hij) hx)]

/-- A locally finite output coefficient equals its ordinary finite truncation
at any point belonging to the target image. -/
theorem kernelSum_localCoefficients {imageA : ι → Set X} {imageB : κ → Set X}
    (K : ι → κ →₀ R)
    (hK : ∀ i j, j ∈ (K i).support → imageB j ⊆ imageA i)
    (c : LocallyFiniteChains.Cycles.SpatialSupport.module R imageA) {x : X} {j : κ} (hx : x ∈ imageB j) :
    kernelSum K (localCoefficients c x) j = kernelSum K c j := by
  classical
  exact kernelSum_congr_at K hK (fun i hi => by simp [hi]) hx

/-- Equality of subordinate operations can be checked on ordinary finite
coefficients; the source space need not be compact. -/
theorem kernelOperation_ext {imageA : ι → Set X} {imageB : κ → Set X}
    (K L : ι → κ →₀ R)
    (hK : ∀ i j, j ∈ (K i).support → imageB j ⊆ imageA i)
    (hL : ∀ i j, j ∈ (L i).support → imageB j ⊆ imageA i)
    (hne : ∀ j, (imageB j).Nonempty)
    (h : Finsupp.linearCombination R K = Finsupp.linearCombination R L) :
    kernelOperation K hK hne = kernelOperation L hL hne := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  funext j
  obtain ⟨x, hx⟩ := hne j
  change kernelSum K c j = kernelSum L c j
  rw [← kernelSum_localCoefficients K hK c hx,
    ← kernelSum_localCoefficients L hL c hx]
  have hh := congrArg (fun z : LocallyFiniteChains.Cycles.SpatialSupport.module R imageB => z j)
    ((kernelOperation_ofFinsupp K hK hne (localCoefficients c x)).trans
      ((congrArg (fun f : (ι →₀ R) →ₗ[R] (κ →₀ R) =>
        LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp imageB (f (localCoefficients c x))) h).trans
          (kernelOperation_ofFinsupp L hL hne (localCoefficients c x)).symm))
  exact hh

/-- Containment is unchanged by replacing a kernel by an equal one. -/
theorem kernelOperation_congr {imageA : ι → Set X} {imageB : κ → Set X}
    {K L : ι → κ →₀ R} (h : K = L)
    (hK : ∀ i j, j ∈ (K i).support → imageB j ⊆ imageA i)
    (hL : ∀ i j, j ∈ (L i).support → imageB j ⊆ imageA i)
    (hne : ∀ j, (imageB j).Nonempty) :
    kernelOperation K hK hne = kernelOperation L hL hne := by
  subst L
  rfl

omit [TopologicalSpace X] in
theorem zeroKernel_subordinate (imageA : ι → Set X) (imageB : κ → Set X) :
    ∀ i j, j ∈ (0 : κ →₀ R).support → imageB j ⊆ imageA i := by
  simp

@[simp]
theorem kernelOperation_zero (imageA : ι → Set X) (imageB : κ → Set X)
    (hne : ∀ j, (imageB j).Nonempty) :
    kernelOperation (fun _ : ι => (0 : κ →₀ R))
      (zeroKernel_subordinate imageA imageB) hne = 0 := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  funext j
  simp [kernelOperation_apply]

omit [TopologicalSpace X] in
theorem identityKernel_subordinate (imageA : ι → Set X) :
    ∀ i j, j ∈ (Finsupp.single i (1 : R)).support → imageA j ⊆ imageA i := by
  classical
  intro i j hj
  have hji : j = i := by
    by_contra hn
    simp only [Finsupp.mem_support_iff, Finsupp.single_eq_of_ne hn, ne_eq,
      not_true_eq_false] at hj
  subst j
  exact Subset.rfl

@[simp]
theorem kernelOperation_id (imageA : ι → Set X)
    (hne : ∀ i, (imageA i).Nonempty) :
    kernelOperation (fun i => Finsupp.single i (1 : R))
      (identityKernel_subordinate imageA) hne = LinearMap.id := by
  classical
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  funext j
  change (∑ᶠ i, c i * Finsupp.single i (1 : R) j) = c j
  rw [finsum_eq_single _ j]
  · simp
  · intro i hi
    simp [hi]

omit [TopologicalSpace X] in
theorem addKernel_subordinate {imageA : ι → Set X} {imageB : κ → Set X}
    (K L : ι → κ →₀ R)
    (hK : ∀ i j, j ∈ (K i).support → imageB j ⊆ imageA i)
    (hL : ∀ i j, j ∈ (L i).support → imageB j ⊆ imageA i) :
    ∀ i j, j ∈ (K i + L i).support → imageB j ⊆ imageA i := by
  intro i j hj
  by_cases hij : K i j = 0
  · apply hL i j
    simpa only [Finsupp.mem_support_iff, Finsupp.add_apply, hij, zero_add] using hj
  · exact hK i j (Finsupp.mem_support_iff.mpr hij)

/-- Addition of finite kernels commutes with locally finite extension. -/
theorem kernelOperation_add {imageA : ι → Set X} {imageB : κ → Set X}
    (K L : ι → κ →₀ R)
    (hK : ∀ i j, j ∈ (K i).support → imageB j ⊆ imageA i)
    (hL : ∀ i j, j ∈ (L i).support → imageB j ⊆ imageA i)
    (hne : ∀ j, (imageB j).Nonempty) :
    kernelOperation (fun i => K i + L i) (addKernel_subordinate K L hK hL) hne =
      kernelOperation K hK hne + kernelOperation L hL hne := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  funext j
  change (∑ᶠ i, c i * (K i + L i) j) =
    (∑ᶠ i, c i * K i j) + (∑ᶠ i, c i * L i j)
  simp only [Finsupp.add_apply, mul_add]
  exact finsum_add_distrib (kernelTerm_hasFiniteSupport K hK hne c j)
    (kernelTerm_hasFiniteSupport L hL hne c j)

omit [TopologicalSpace X] in
/-- The ordinary finite composite kernel is again spatially subordinate. -/
theorem compKernel_subordinate {imageA : ι → Set X} {imageB : κ → Set X}
    {imageC : μ → Set X} (K : ι → κ →₀ R) (L : κ → μ →₀ R)
    (hK : ∀ i j, j ∈ (K i).support → imageB j ⊆ imageA i)
    (hL : ∀ j k, k ∈ (L j).support → imageC k ⊆ imageB j) :
    ∀ i k, k ∈ (Finsupp.linearCombination R L (K i)).support →
      imageC k ⊆ imageA i := by
  intro i k hk
  obtain ⟨j, hj, hkj⟩ := Finsupp.mem_support_finsetSum k hk
  exact (hL j k (Finsupp.support_smul hkj)).trans (hK i j hj)

/-- Locally finite extension preserves composition. The proof reduces each
coefficient to a finite input at a point of the output simplex. -/
theorem kernelOperation_comp {imageA : ι → Set X} {imageB : κ → Set X}
    {imageC : μ → Set X} (K : ι → κ →₀ R) (L : κ → μ →₀ R)
    (hK : ∀ i j, j ∈ (K i).support → imageB j ⊆ imageA i)
    (hL : ∀ j k, k ∈ (L j).support → imageC k ⊆ imageB j)
    (hneB : ∀ j, (imageB j).Nonempty) (hneC : ∀ k, (imageC k).Nonempty) :
    (kernelOperation L hL hneC).comp (kernelOperation K hK hneB) =
      kernelOperation (fun i => Finsupp.linearCombination R L (K i))
        (compKernel_subordinate K L hK hL) hneC := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  funext k
  obtain ⟨x, hx⟩ := hneC k
  let c' := localCoefficients c x
  have hfirst : kernelSum L (kernelOperation K hK hneB c) k =
      kernelSum L (kernelOperation K hK hneB (LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp imageA c')) k := by
    apply kernelSum_congr_at L hL (x := x) _ hx
    intro j hj
    exact (kernelSum_localCoefficients K hK c hj).symm
  have hlast := kernelSum_localCoefficients
    (fun i => Finsupp.linearCombination R L (K i))
    (compKernel_subordinate K L hK hL) c hx
  change kernelSum L (kernelOperation K hK hneB c) k = _
  rw [hfirst]
  change kernelOperation L hL hneC
    (kernelOperation K hK hneB (LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp imageA c')) k = _
  rw [kernelOperation_ofFinsupp, kernelOperation_ofFinsupp]
  have hfinite : Finsupp.linearCombination R L (Finsupp.linearCombination R K c') =
      Finsupp.linearCombination R (fun i => Finsupp.linearCombination R L (K i)) c' :=
    Finsupp.apply_linearCombination R (Finsupp.linearCombination R L) K c'
  rw [hfinite]
  exact (congrArg (fun z : LocallyFiniteChains.Cycles.SpatialSupport.module R imageC => z k)
    (kernelOperation_ofFinsupp
      (fun i => Finsupp.linearCombination R L (K i))
      (compKernel_subordinate K L hK hL) hneC c')).symm.trans hlast

/-- An operation is spatially local when its coefficient at an image
containing `x` only depends on source coefficients whose images contain `x`. -/
def IsSpatiallyLocal {imageA : ι → Set X} {imageB : κ → Set X}
    (F : LocallyFiniteChains.Cycles.SpatialSupport.module R imageA →ₗ[R] LocallyFiniteChains.Cycles.SpatialSupport.module R imageB) : Prop :=
  ∀ (x : X) (c d : LocallyFiniteChains.Cycles.SpatialSupport.module R imageA),
    (∀ i, x ∈ imageA i → c i = d i) →
      ∀ j, x ∈ imageB j → F c j = F d j

/-- Every subordinate kernel extension satisfies the explicit locality law. -/
theorem kernelOperation_isSpatiallyLocal {imageA : ι → Set X} {imageB : κ → Set X}
    (K : ι → κ →₀ R)
    (hK : ∀ i j, j ∈ (K i).support → imageB j ⊆ imageA i)
    (hne : ∀ j, (imageB j).Nonempty) :
    IsSpatiallyLocal (kernelOperation K hK hne) := by
  intro x c d hcd j hx
  exact kernelSum_congr_at K hK hcd hx

/-- The single-index spatial pushforward is also local. -/
theorem pushforward_isSpatiallyLocal {imageA : ι → Set X} {imageB : κ → Set X}
    (f : ι → κ) (hf : ∀ i, imageB (f i) ⊆ imageA i)
    (hne : ∀ j, (imageB j).Nonempty) : IsSpatiallyLocal (LocallyFiniteChains.Cycles.SpatialSupport.pushforward (R := R) f hf hne) := by
  intro x c d hcd j hx
  exact finsum_mem_congr rfl (fun i hi => hcd i (hf i (hi.symm ▸ hx)))

/-- Local linear operations are uniquely determined by their restriction to
ordinary finite coefficients, without any compactness hypothesis. -/
theorem IsSpatiallyLocal.ext {imageA : ι → Set X} {imageB : κ → Set X}
    {F G : LocallyFiniteChains.Cycles.SpatialSupport.module R imageA →ₗ[R] LocallyFiniteChains.Cycles.SpatialSupport.module R imageB}
    (hF : IsSpatiallyLocal F) (hG : IsSpatiallyLocal G)
    (hne : ∀ j, (imageB j).Nonempty)
    (hfinite : ∀ c : ι →₀ R, F (LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp imageA c) = G (LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp imageA c)) : F = G := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  funext j
  obtain ⟨x, hx⟩ := hne j
  have hloc : ∀ i, x ∈ imageA i → c i = LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp imageA (localCoefficients c x) i := by
    intro i hi
    simp [hi]
  exact (hF x c _ hloc j hx).trans
    ((congrArg (fun z : LocallyFiniteChains.Cycles.SpatialSupport.module R imageB => z j) (hfinite (localCoefficients c x))).trans
      (hG x c _ hloc j hx).symm)

theorem IsSpatiallyLocal.zero (imageA : ι → Set X) (imageB : κ → Set X) :
    IsSpatiallyLocal (0 : LocallyFiniteChains.Cycles.SpatialSupport.module R imageA →ₗ[R] LocallyFiniteChains.Cycles.SpatialSupport.module R imageB) := by
  intro _ _ _ _ _ _
  rfl

theorem IsSpatiallyLocal.id (imageA : ι → Set X) :
    IsSpatiallyLocal (LinearMap.id : LocallyFiniteChains.Cycles.SpatialSupport.module R imageA →ₗ[R] LocallyFiniteChains.Cycles.SpatialSupport.module R imageA) := by
  intro _ _ _ hcd _ hx
  exact hcd _ hx

theorem IsSpatiallyLocal.add {imageA : ι → Set X} {imageB : κ → Set X}
    {F G : LocallyFiniteChains.Cycles.SpatialSupport.module R imageA →ₗ[R] LocallyFiniteChains.Cycles.SpatialSupport.module R imageB}
    (hF : IsSpatiallyLocal F) (hG : IsSpatiallyLocal G) : IsSpatiallyLocal (F + G) := by
  intro x c d hcd j hx
  exact congrArg₂ (· + ·) (hF x c d hcd j hx) (hG x c d hcd j hx)

theorem IsSpatiallyLocal.comp {imageA : ι → Set X} {imageB : κ → Set X}
    {imageC : μ → Set X}
    {F : LocallyFiniteChains.Cycles.SpatialSupport.module R imageA →ₗ[R] LocallyFiniteChains.Cycles.SpatialSupport.module R imageB}
    {G : LocallyFiniteChains.Cycles.SpatialSupport.module R imageB →ₗ[R] LocallyFiniteChains.Cycles.SpatialSupport.module R imageC}
    (hG : IsSpatiallyLocal G) (hF : IsSpatiallyLocal F) : IsSpatiallyLocal (G.comp F) := by
  intro x c d hcd k hx
  exact hG x (F c) (F d) (hF x c d hcd) k hx

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteOperation.Cycles.SpatialSupport
