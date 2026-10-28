import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCap
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompactRestriction
import OAI.AlgebraicTopology.Cohomology.Singular.RelativeSequence

/-! # Compact Support Cap -/

namespace OAI.AlgebraicTopology.Products.CompactSupportCap

noncomputable section

/-!
# Compactly supported cochains cap locally finite chains to finite chains

The support condition is the actual kernel of restriction to the complement.
Its simplexwise meaning is proved below. The finite-chain factorization uses
the existing compact truncation of locally finite coefficients; no infinite
sum is interpreted as an ordinary chain.
-/

open _root_.CategoryTheory Set
open scoped Simplicial BigOperators
open OAI.AlgebraicTopology.Cohomology.Singular.RelativeSequence

variable {R : Type} [CommRing R]

/-- Ordinary cochains supported in `K`, defined by the actual restriction
map to its complement. Compactness is not needed for this definition. -/
abbrev cochainsSupportedIn (X : TopCat.{0}) (K : Set X) (p : ℕ) :
    Submodule R ((Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p) :=
  LinearMap.ker ((Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of R R) X Kᶜ).f p).hom

/-- The actual support kernel consists exactly of cochains vanishing on
every simplex whose whole image is outside `K`. -/
theorem mem_cochainsSupportedIn_iff (X : TopCat.{0}) (K : Set X) (p : ℕ)
    (c : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p) :
    c ∈ cochainsSupportedIn X K p ↔
      ∀ s : (TopCat.toSSet.obj X) _⦋p⦌,
        AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.singularSimplexImage X p s ⊆ Kᶜ →
          Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) (ModuleCat.of R R) s c = 0 := by
  change ((Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of R R) X Kᶜ).f p) c = 0 ↔ _
  constructor
  · intro hc s hs
    obtain ⟨t, ht⟩ := (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.mem_subspaceSingularSubcomplex X Kᶜ (.op ⦋p⦌) s).mpr hs
    have hc' : ((Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of R R)
        (TopCat.toSSet.map (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X Kᶜ))).f p) c = 0 := hc
    have h := Cohomology.Singular.Formulas.evaluation_pullback_apply (ModuleCat.of R R)
      (TopCat.toSSet.map (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X Kᶜ)) c t
    simpa only [hc', map_zero, ht] using h.symm
  · intro hc
    apply Cup.cochain_ext (TopCat.toSSet.obj (TopCat.of (Kᶜ : Set X))) (ModuleCat.of R R)
    intro t
    have ht : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.singularSimplexImage X p
        ((TopCat.toSSet.map (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X Kᶜ)).app _ t) ⊆ Kᶜ :=
      (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.mem_subspaceSingularSubcomplex X Kᶜ (.op ⦋p⦌) _).mp ⟨t, rfl⟩
    have h := Cohomology.Singular.Formulas.evaluation_pullback_apply (ModuleCat.of R R)
      (TopCat.toSSet.map (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X Kᶜ)) c t
    rw [map_zero]
    exact h.trans (hc _ ht)

/-- This support submodule is exactly the image of genuine relative cochains. -/
theorem cochainsSupportedIn_eq_relative_range (X : TopCat.{0}) (K : Set X) (p : ℕ) :
    cochainsSupportedIn (R := R) X K p =
      LinearMap.range ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of R R) X Kᶜ).f p).hom :=
  (Cohomology.Singular.RelativeSequence.relativeCochainInclusion_range (ModuleCat.of R R) X Kᶜ p).symm

/-- The actual relative-cochain inclusion, with codomain restricted to the
proved support kernel. -/
def relativeCochainToSupported (X : TopCat.{0}) (K : Set X) (p : ℕ) :
    (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X Kᶜ).X p →ₗ[R]
      cochainsSupportedIn (R := R) X K p :=
  (((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of R R) X Kᶜ).f p).hom.codRestrict
    (cochainsSupportedIn X K p) (fun c => by
      rw [cochainsSupportedIn_eq_relative_range]
      exact ⟨c, rfl⟩))

@[simp]
theorem relativeCochainToSupported_val (X : TopCat.{0}) (K : Set X) (p : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X Kᶜ).X p) :
    (relativeCochainToSupported X K p c).val =
      ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of R R) X Kᶜ).f p) c := rfl

/-- The ordinary coboundary restricts to cochains with the same support set. -/
def supportedCochainD (X : TopCat.{0}) (K : Set X) (p : ℕ) :
    cochainsSupportedIn (R := R) X K p →ₗ[R] cochainsSupportedIn (R := R) X K (p + 1) :=
  ((((Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).d p (p + 1)).hom.comp
    (cochainsSupportedIn X K p).subtype).codRestrict
      (cochainsSupportedIn X K (p + 1)) (fun c => by
        change ((Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of R R) X Kᶜ).f (p + 1))
          (((Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).d p (p + 1)) c.val) = 0
        have hc : ((Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of R R) X Kᶜ).f p) c.val = 0 :=
          c.property
        have h := ConcreteCategory.congr_hom
          ((Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of R R) X Kᶜ).comm p (p + 1)) c.val
        simpa only [ConcreteCategory.comp_apply, hc, map_zero] using h.symm))

@[simp]
theorem supportedCochainD_val (X : TopCat.{0}) (K : Set X) (p : ℕ)
    (c : cochainsSupportedIn (R := R) X K p) :
    (supportedCochainD X K p c).val =
      ((Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).d p (p + 1)) c.val := rfl

/-- The supported-cochain differential is the actual relative differential
under the canonical relative inclusion. -/
theorem relativeCochainToSupported_d (X : TopCat.{0}) (K : Set X) (p : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X Kᶜ).X p) :
    supportedCochainD X K p (relativeCochainToSupported X K p c) =
      relativeCochainToSupported X K (p + 1)
        (((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X Kᶜ).d p (p + 1)) c) := by
  apply Subtype.ext
  exact ConcreteCategory.congr_hom
    ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of R R) X Kᶜ).comm p (p + 1)) c

/-- The existing compact coefficient truncation, expressed in the actual
ordinary singular-chain module over any commutative coefficient ring. -/
def compactSingularTruncation (X : TopCat.{0}) (K : Set X) (hK : IsCompact K) (n : ℕ) :
    AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n →ₗ[R] (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X n :=
  (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R X n).symm.toLinearMap.comp
    (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles.SpatialSupport.compactTruncation (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.singularSimplexImage X n) K hK)

@[simp]
theorem ordinaryToLocallyFinite_compactSingularTruncation
    (X : TopCat.{0}) (K : Set X) (hK : IsCompact K) (n : ℕ)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n) :
    AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X n (compactSingularTruncation X K hK n z) =
      AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.singularSimplexImage X n)
        (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles.SpatialSupport.compactTruncation (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.singularSimplexImage X n) K hK z) := by
  simp only [AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite, compactSingularTruncation, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

/-- A compactly supported ordinary cochain caps a locally finite chain to
an actual finite ordinary chain. -/
def compactSupportCap (X : TopCat.{0}) (K : Set X) (hK : IsCompact K) (p q : ℕ) :
    cochainsSupportedIn (R := R) X K p →ₗ[R]
      AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X (p + q) →ₗ[R] (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X q :=
  (((Cap.singularCap X p q).comp (cochainsSupportedIn X K p).subtype).compl₂
    (compactSingularTruncation X K hK (p + q)))

@[simp]
theorem compactSupportCap_apply (X : TopCat.{0}) (K : Set X) (hK : IsCompact K) (p q : ℕ)
    (c : cochainsSupportedIn (R := R) X K p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X (p + q)) :
    compactSupportCap X K hK p q c z =
      Cap.singularCap X p q c.val (compactSingularTruncation X K hK (p + q) z) := rfl

/-- Outside the compact support set, the actual cap kernel is zero. -/
theorem supportedCapKernel_eq_zero (X : TopCat.{0}) (K : Set X) (p q : ℕ)
    (c : cochainsSupportedIn (R := R) X K p)
    (s : (TopCat.toSSet.obj X) _⦋p + q⦌)
    (hs : ¬(AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.singularSimplexImage X (p + q) s ∩ K).Nonempty) :
    AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCap.Cycles.locallyFiniteCapKernel X p q c.val s = 0 := by
  have hfront : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.singularSimplexImage X p (SimplexFaceIdentities.frontFace (TopCat.toSSet.obj X) p q s) ⊆ Kᶜ := by
    intro x hx hxK
    apply hs
    exact ⟨x, AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.singularSimplexImage_map_subset X (SimplexFaceIdentities.frontInclusion p q).op s hx, hxK⟩
  have hc := (mem_cochainsSupportedIn_iff X K p c.val).mp c.property _ hfront
  simp only [AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCap.Cycles.locallyFiniteCapKernel, hc, Finsupp.single_zero]

/-- A compactly supported cochain ignores every source coefficient removed
by compact truncation. This is equality of the genuine finite coefficient sums. -/
theorem supportedCap_eq_compactTruncation (X : TopCat.{0}) (K : Set X) (hK : IsCompact K)
    (p q : ℕ) (c : cochainsSupportedIn (R := R) X K p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X (p + q)) :
    AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCap.Cycles.locallyFiniteCap X p q c.val z =
      AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCap.Cycles.locallyFiniteCap X p q c.val
        (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X (p + q) (compactSingularTruncation X K hK (p + q) z)) := by
  rw [ordinaryToLocallyFinite_compactSingularTruncation]
  apply Subtype.ext
  funext t
  change (∑ᶠ s, z s * AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCap.Cycles.locallyFiniteCapKernel X p q c.val s t) =
    ∑ᶠ s, AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.singularSimplexImage X (p + q))
      (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles.SpatialSupport.compactTruncation (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.singularSimplexImage X (p + q)) K hK z) s *
        AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCap.Cycles.locallyFiniteCapKernel X p q c.val s t
  apply finsum_congr
  intro s
  by_cases hs : (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.singularSimplexImage X (p + q) s ∩ K).Nonempty
  · simp only [AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp_apply, AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles.SpatialSupport.compactTruncation_apply, ite_eq_left hs]
  · rw [supportedCapKernel_eq_zero X K p q c s hs]
    simp only [Finsupp.zero_apply, mul_zero]

/-- Including the finite output recovers the original locally finite cap product. -/
theorem compactSupportCap_inclusion (X : TopCat.{0}) (K : Set X) (hK : IsCompact K)
    (p q : ℕ) (c : cochainsSupportedIn (R := R) X K p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X (p + q)) :
    AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X q (compactSupportCap X K hK p q c z) =
      AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCap.Cycles.locallyFiniteCap X p q c.val z := by
  rw [compactSupportCap_apply]
  rw [← AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCap.Cycles.locallyFiniteCap_ordinary]
  exact (supportedCap_eq_compactTruncation X K hK p q c z).symm

/-- The locally finite cap image lies in the actual ordinary-chain range. -/
theorem supportedCap_mem_ordinary_range (X : TopCat.{0}) (K : Set X) (hK : IsCompact K)
    (p q : ℕ) (c : cochainsSupportedIn (R := R) X K p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X (p + q)) :
    AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCap.Cycles.locallyFiniteCap X p q c.val z ∈ LinearMap.range (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X q) :=
  ⟨compactSupportCap X K hK p q c z, compactSupportCap_inclusion X K hK p q c z⟩

/-- The output coefficient function has genuinely finite support. -/
theorem supportedCap_finite_support (X : TopCat.{0}) (K : Set X) (hK : IsCompact K)
    (p q : ℕ) (c : cochainsSupportedIn (R := R) X K p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X (p + q)) :
    (Function.support (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCap.Cycles.locallyFiniteCap X p q c.val z : (TopCat.toSSet.obj X) _⦋q⦌ → R)).Finite := by
  rw [← compactSupportCap_inclusion X K hK p q c z]
  exact (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R X q
    (compactSupportCap X K hK p q c z)).hasFiniteSupport

/-- On ordinary finite input, the factorization is exactly the previously
checked ordinary cap product. -/
theorem compactSupportCap_ordinary (X : TopCat.{0}) (K : Set X) (hK : IsCompact K)
    (p q : ℕ) (c : cochainsSupportedIn (R := R) X K p)
    (z : (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X (p + q)) :
    compactSupportCap X K hK p q c (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X (p + q) z) =
      Cap.singularCap X p q c.val z := by
  apply AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComparison.Cycles.ordinaryToLocallyFinite_injective R X q
  rw [compactSupportCap_inclusion, AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCap.Cycles.locallyFiniteCap_ordinary]

/-- Enlarging or changing the chosen compact support set does not change
the finite result when the underlying ordinary cochain is the same. -/
theorem compactSupportCap_eq_of_cochain_eq (X : TopCat.{0}) (K L : Set X)
    (hK : IsCompact K) (hL : IsCompact L) (p q : ℕ)
    (c : cochainsSupportedIn (R := R) X K p) (d : cochainsSupportedIn (R := R) X L p)
    (hcd : c.val = d.val) (z : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X (p + q)) :
    compactSupportCap X K hK p q c z = compactSupportCap X L hL p q d z := by
  apply AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComparison.Cycles.ordinaryToLocallyFinite_injective R X q
  rw [compactSupportCap_inclusion, compactSupportCap_inclusion, hcd]

/-- The finite factorization retains the genuine signed cap boundary law.
The equality is in the ordinary finite singular-chain module. -/
theorem compactSupportCap_boundary (X : TopCat.{0}) (K : Set X) (hK : IsCompact K)
    (p q : ℕ) (c : cochainsSupportedIn (R := R) X K p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X (p + q + 1)) :
    compactSupportCap X K hK p q c (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.locallyFiniteBoundary R X (p + q) z) =
      compactSupportCap X K hK (p + 1) q (supportedCochainD X K p c)
        (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCap.Cycles.locallyFiniteChainCast X (by omega : p + q + 1 = (p + 1) + q) z) +
      ((-1 : ℤ) ^ p) • ((Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).d (q + 1) q
        (compactSupportCap X K hK p (q + 1) c z)) := by
  apply AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComparison.Cycles.ordinaryToLocallyFinite_injective R X q
  simp only [map_add, map_zsmul]
  rw [compactSupportCap_inclusion, compactSupportCap_inclusion,
    ← AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCap.Cycles.locallyFiniteBoundary_ordinary]
  erw [compactSupportCap_inclusion X K hK p (q + 1) c z]
  exact AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCap.Cycles.locallyFiniteCap_boundary X p q c.val z

/-- The boundary law solved for the boundary of the resulting finite chain. -/
theorem boundary_compactSupportCap (X : TopCat.{0}) (K : Set X) (hK : IsCompact K)
    (p q : ℕ) (c : cochainsSupportedIn (R := R) X K p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X (p + q + 1)) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).d (q + 1) q
        (compactSupportCap X K hK p (q + 1) c z) =
      ((-1 : ℤ) ^ p) •
        (compactSupportCap X K hK p q c (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.locallyFiniteBoundary R X (p + q) z) -
          compactSupportCap X K hK (p + 1) q (supportedCochainD X K p c)
            (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCap.Cycles.locallyFiniteChainCast X (by omega : p + q + 1 = (p + 1) + q) z)) := by
  rw [compactSupportCap_boundary X K hK p q c z, add_sub_cancel_left, smul_smul]
  have hs : ((-1 : ℤ) ^ p) * ((-1 : ℤ) ^ p) = 1 := by
    rw [← mul_pow]
    simp
  rw [hs, one_smul]

end

end OAI.AlgebraicTopology.Products.CompactSupportCap
