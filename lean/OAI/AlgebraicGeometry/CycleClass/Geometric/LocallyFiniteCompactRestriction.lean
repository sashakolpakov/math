import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComparison
import OAI.AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeChainSupport
import OAI.AlgebraicGeometry.CycleClass.Geometric.Point

/-! # Locally Finite Compact Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles

noncomputable section

/-!
# Restriction of locally finite chains near a compact set

Only finitely many nonzero simplices of a spatially locally finite chain meet
a fixed compact set. Truncation to those simplices is therefore an ordinary
finite chain. After quotienting by simplices in the complement, this gives the
canonical restriction to relative chains.
-/

open Set Function _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial BigOperators Classical

namespace SpatialSupport

variable {X ι κ : Type*} [TopologicalSpace X]
variable {R : Type*} [Semiring R]

/-- A compact set meets only finitely many nonzero images of a spatially
locally finite coefficient family. -/
theorem compactTruncation_finite {image : ι → Set X} (K : Set X) (hK : IsCompact K)
    (c : LocallyFiniteChains.Cycles.SpatialSupport.module R image) :
    (support (fun i => if (image i ∩ K).Nonempty then c i else 0)).Finite := by
  classical
  have hf := c.property.finite_nonempty_inter_compact hK
  apply hf.subset
  intro i hi
  change (if (image i ∩ K).Nonempty then c i else 0) ≠ 0 at hi
  by_cases hmeet : (image i ∩ K).Nonempty
  · have hci : c i ≠ 0 := by simpa only [ite_eq_left hmeet] using hi
    obtain ⟨x, hxi, hxK⟩ := hmeet
    exact ⟨x, ⟨hci, hxi⟩, hxK⟩
  · simp only [ite_eq_right hmeet, ne_eq, not_true_eq_false] at hi

/-- Literal coefficient truncation to the nonzero spatial images meeting a
compact set, with its finite-support proof. -/
def compactTruncation (image : ι → Set X) (K : Set X) (hK : IsCompact K) :
    LocallyFiniteChains.Cycles.SpatialSupport.module R image →ₗ[R] (ι →₀ R) where
  toFun c := Finsupp.ofSupportFinite
    (fun i => if (image i ∩ K).Nonempty then c i else 0)
    (compactTruncation_finite K hK c)
  map_add' c d := by
    classical
    apply Finsupp.ext
    intro i
    change (if (image i ∩ K).Nonempty then c i + d i else 0) =
      (if (image i ∩ K).Nonempty then c i else 0) +
        (if (image i ∩ K).Nonempty then d i else 0)
    split_ifs <;> simp
  map_smul' r c := by
    classical
    apply Finsupp.ext
    intro i
    change (if (image i ∩ K).Nonempty then r • c i else 0) =
      r • (if (image i ∩ K).Nonempty then c i else 0)
    split_ifs <;> simp

@[simp]
theorem compactTruncation_apply (image : ι → Set X) (K : Set X) (hK : IsCompact K)
    (c : LocallyFiniteChains.Cycles.SpatialSupport.module R image) (i : ι) :
    compactTruncation image K hK c i =
      if (image i ∩ K).Nonempty then c i else 0 := rfl

/-- Truncation preserves every coefficient whose spatial image meets the
compact set. -/
theorem compactTruncation_agrees (image : ι → Set X) (K : Set X) (hK : IsCompact K)
    (c : LocallyFiniteChains.Cycles.SpatialSupport.module R image) (i : ι) (hi : (image i ∩ K).Nonempty) :
    compactTruncation image K hK c i = c i := by
  rw [compactTruncation_apply, ite_eq_left hi]

/-- A spatially subordinate index pushforward depends near K only on the
source coefficients whose images meet K. -/
theorem pushforward_agrees_of_agrees {imageA : ι → Set X} {imageB : κ → Set X}
    (f : ι → κ) (himage : ∀ i, imageB (f i) ⊆ imageA i)
    (hne : ∀ j, (imageB j).Nonempty) (K : Set X)
    (c d : LocallyFiniteChains.Cycles.SpatialSupport.module R imageA)
    (hcd : ∀ i, (imageA i ∩ K).Nonempty → c i = d i)
    (j : κ) (hj : (imageB j ∩ K).Nonempty) :
    LocallyFiniteChains.Cycles.SpatialSupport.pushforward f himage hne c j = LocallyFiniteChains.Cycles.SpatialSupport.pushforward f himage hne d j := by
  apply finsum_mem_congr rfl
  intro i hi
  obtain ⟨x, hxj, hxK⟩ := hj
  apply hcd i
  exact ⟨x, himage i ((show f i = j from hi).symm ▸ hxj), hxK⟩

end SpatialSupport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Each actual singular face preserves agreement of locally finite
coefficients near an arbitrary subset. -/
theorem locallyFiniteFace_agrees_of_agrees {R : Type*} [Semiring R]
    (X : TopCat.{0}) (K : Set X) (n : ℕ) (i : Fin (n + 2))
    (c d : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X (n + 1))
    (hcd : ∀ σ, (LocallyFiniteChains.Cycles.singularSimplexImage X (n + 1) σ ∩ K).Nonempty → c σ = d σ)
    (τ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌))
    (hτ : (LocallyFiniteChains.Cycles.singularSimplexImage X n τ ∩ K).Nonempty) :
    LocallyFiniteChains.Cycles.locallyFiniteFace R X n i c τ = LocallyFiniteChains.Cycles.locallyFiniteFace R X n i d τ :=
  SpatialSupport.pushforward_agrees_of_agrees ((TopCat.toSSet.obj X).δ i)
    (LocallyFiniteChains.Cycles.singularSimplexImage_face_subset X n i) (LocallyFiniteChains.Cycles.singularSimplexImage_nonempty X n)
    K c d hcd τ hτ

/-- The actual alternating singular boundary preserves agreement near K. -/
theorem locallyFiniteBoundary_agrees_of_agrees {R : Type*} [CommRing R]
    (X : TopCat.{0}) (K : Set X) (n : ℕ)
    (c d : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X (n + 1))
    (hcd : ∀ σ, (LocallyFiniteChains.Cycles.singularSimplexImage X (n + 1) σ ∩ K).Nonempty → c σ = d σ)
    (τ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌))
    (hτ : (LocallyFiniteChains.Cycles.singularSimplexImage X n τ ∩ K).Nonempty) :
    LocallyFiniteChains.Cycles.locallyFiniteBoundary R X n c τ = LocallyFiniteChains.Cycles.locallyFiniteBoundary R X n d τ := by
  simp only [LocallyFiniteChains.Cycles.locallyFiniteBoundary, LinearMap.sum_apply, LinearMap.smul_apply,
    Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [locallyFiniteFace_agrees_of_agrees X K n i c d hcd τ hτ]

/-- Ordinary finite-chain truncation of an integral locally finite chain
to the simplices that meet a compact set. -/
def locallyFiniteCompactTruncation (X : TopCat.{0}) (K : Set X) (hK : IsCompact K)
    (n : ℕ) : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ X n →ₗ[ℤ] (LocalHomology.Cycles.integralSingularChains X).X n :=
  (LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℤ X n).symm.toLinearMap.comp
    (SpatialSupport.compactTruncation (LocallyFiniteChains.Cycles.singularSimplexImage X n) K hK)

@[simp]
theorem locallyFiniteCompactTruncation_coefficients (X : TopCat.{0})
    (K : Set X) (hK : IsCompact K) (n : ℕ) (c : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ X n)
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌)) :
    LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℤ X n (locallyFiniteCompactTruncation X K hK n c) σ =
      if (LocallyFiniteChains.Cycles.singularSimplexImage X n σ ∩ K).Nonempty then c σ else 0 := by
  change (LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℤ X n)
      ((LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℤ X n).symm
        (SpatialSupport.compactTruncation (LocallyFiniteChains.Cycles.singularSimplexImage X n) K hK c)) σ = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Ordinary boundary coefficients are the locally finite boundary
coefficients of the canonical ordinary-chain inclusion. -/
theorem ordinarySingularBoundary_coefficients (X : TopCat.{0}) (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X (n + 1))
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌)) :
    LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℤ X n ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n c) σ =
      LocallyFiniteChains.Cycles.locallyFiniteBoundary ℤ X n (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite ℤ X (n + 1) c) σ := by
  have h := congrArg ModuleCat.Hom.hom (LocallyFiniteComparison.Cycles.ordinaryToLocallyFinite_comm ℤ X n)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex_d] at h
  have hc := LinearMap.congr_fun h c
  change LocallyFiniteChains.Cycles.locallyFiniteBoundary ℤ X n (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite ℤ X (n + 1) c) =
    LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite ℤ X n ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n c) at hc
  exact congrArg (fun z : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ X n => z σ) hc.symm

/-- Taking the ordinary boundary after compact truncation preserves every
boundary coefficient whose simplex image meets the compact set. -/
theorem locallyFiniteCompactTruncation_boundary_agrees (X : TopCat.{0})
    (K : Set X) (hK : IsCompact K) (n : ℕ)
    (c : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ X (n + 1))
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌))
    (hσ : (LocallyFiniteChains.Cycles.singularSimplexImage X n σ ∩ K).Nonempty) :
    LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℤ X n
        ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n
          (locallyFiniteCompactTruncation X K hK (n + 1) c)) σ =
      LocallyFiniteChains.Cycles.locallyFiniteBoundary ℤ X n c σ := by
  rw [ordinarySingularBoundary_coefficients]
  apply locallyFiniteBoundary_agrees_of_agrees X K n _ c _ σ hσ
  intro τ hτ
  change LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℤ X (n + 1)
      (locallyFiniteCompactTruncation X K hK (n + 1) c) τ = c τ
  rw [locallyFiniteCompactTruncation_coefficients, ite_eq_left hτ]

/-- The canonical degree map to the actual relative-chain quotient. Its
chain compatibility follows from the proved locality of singular faces. -/
def locallyFiniteCompactRestrictionDegree (X : TopCat.{0})
    (K : Set X) (hK : IsCompact K) (n : ℕ) :
    LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ X n →ₗ[ℤ] (LocalHomology.Cycles.relativeSingularChains X Kᶜ).X n :=
  ((LocalHomology.Cycles.relativeChainProjection X Kᶜ).f n).hom.comp (locallyFiniteCompactTruncation X K hK n)

/-- Relative projection only depends on finite-chain coefficients of simplices
whose images meet K. -/
theorem relativeChainProjection_eq_of_agrees_near (X : TopCat.{0}) (K : Set X)
    (n : ℕ) (a b : (LocalHomology.Cycles.integralSingularChains X).X n)
    (hab : ∀ σ, (LocallyFiniteChains.Cycles.singularSimplexImage X n σ ∩ K).Nonempty →
      LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℤ X n a σ =
        LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℤ X n b σ) :
    (LocalHomology.Cycles.relativeChainProjection X Kᶜ).f n a = (LocalHomology.Cycles.relativeChainProjection X Kᶜ).f n b := by
  apply sub_eq_zero.mp
  have hzero := RelativeChainSupport.Cycles.relativeChainProjection_eq_zero_of_supported X Kᶜ n (a - b) (by
    intro σ hσ x hx hxK
    apply hσ
    simp only [map_sub, Finsupp.sub_apply, sub_eq_zero]
    exact hab σ ⟨x, hx, hxK⟩)
  simpa only [map_sub] using hzero

/-- Any ordinary finite chain with the same coefficients near K represents
the compact restriction of a locally finite chain. -/
theorem locallyFiniteCompactRestrictionDegree_eq_of_agrees
    (X : TopCat.{0}) (K : Set X) (hK : IsCompact K) (n : ℕ)
    (c : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ X n) (a : (LocalHomology.Cycles.integralSingularChains X).X n)
    (hca : ∀ σ, (LocallyFiniteChains.Cycles.singularSimplexImage X n σ ∩ K).Nonempty →
      c σ = LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℤ X n a σ) :
    locallyFiniteCompactRestrictionDegree X K hK n c =
      (LocalHomology.Cycles.relativeChainProjection X Kᶜ).f n a := by
  change (LocalHomology.Cycles.relativeChainProjection X Kᶜ).f n
    (locallyFiniteCompactTruncation X K hK n c) = _
  apply relativeChainProjection_eq_of_agrees_near
  intro σ hσ
  rw [locallyFiniteCompactTruncation_coefficients, ite_eq_left hσ]
  exact hca σ hσ

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The truncated boundary and the boundary of truncation agree in the
genuine relative-chain quotient. -/
theorem locallyFiniteCompactRestriction_comm (X : TopCat.{0})
    (K : Set X) (hK : IsCompact K) (n : ℕ) :
    ModuleCat.ofHom (locallyFiniteCompactRestrictionDegree X K hK (n + 1)) ≫
        (LocalHomology.Cycles.relativeSingularChains X Kᶜ).d (n + 1) n =
      (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X).d (n + 1) n ≫
        ModuleCat.ofHom (locallyFiniteCompactRestrictionDegree X K hK n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change ((LocalHomology.Cycles.relativeSingularChains X Kᶜ).d (n + 1) n).hom
      (((LocalHomology.Cycles.relativeChainProjection X Kᶜ).f (n + 1)).hom
        (locallyFiniteCompactTruncation X K hK (n + 1) c)) =
    ((LocalHomology.Cycles.relativeChainProjection X Kᶜ).f n).hom
      (locallyFiniteCompactTruncation X K hK n
        (((LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X).d (n + 1) n).hom c))
  rw [LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex_d]
  calc
    _ = (LocalHomology.Cycles.relativeChainProjection X Kᶜ).f n
        ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n
          (locallyFiniteCompactTruncation X K hK (n + 1) c)) :=
      ConcreteCategory.congr_hom ((LocalHomology.Cycles.relativeChainProjection X Kᶜ).comm (n + 1) n)
        (locallyFiniteCompactTruncation X K hK (n + 1) c)
    _ = _ := by
      apply relativeChainProjection_eq_of_agrees_near
      intro σ hσ
      rw [locallyFiniteCompactTruncation_boundary_agrees X K hK n c σ hσ,
        locallyFiniteCompactTruncation_coefficients, ite_eq_left hσ]
      rfl

/-- Restriction of actual locally finite integral chains to the ordinary
relative chains C(X,X\K), for any compact subset K. -/
def locallyFiniteCompactRestriction (X : TopCat.{0}) (K : Set X) (hK : IsCompact K) :
    LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X ⟶ LocalHomology.Cycles.relativeSingularChains X Kᶜ where
  f n := ModuleCat.ofHom (locallyFiniteCompactRestrictionDegree X K hK n)
  comm' i j hij := by
    change j + 1 = i at hij
    subst i
    exact locallyFiniteCompactRestriction_comm X K hK j

@[simp]
theorem locallyFiniteCompactRestriction_f (X : TopCat.{0})
    (K : Set X) (hK : IsCompact K) (n : ℕ) :
    (locallyFiniteCompactRestriction X K hK).f n =
      ModuleCat.ofHom (locallyFiniteCompactRestrictionDegree X K hK n) := rfl

/-- The canonical compact-support restriction on genuine locally finite
singular homology. -/
abbrev locallyFiniteCompactHomologyRestriction (X : TopCat.{0})
    (K : Set X) (hK : IsCompact K) (n : ℕ) :
    (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X).homology n ⟶ LocalHomology.Cycles.relativeSingularHomology X Kᶜ n :=
  HomologicalComplex.homologyMap (locallyFiniteCompactRestriction X K hK) n

/-- Restricting a locally finite class to a point gives its actual local
integral singular-homology class. -/
abbrev locallyFinitePointHomologyRestriction (X : TopCat.{0}) (x : X) (n : ℕ) :
    (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X).homology n ⟶ LocalHomology.Cycles.localSingularHomology X x n :=
  locallyFiniteCompactHomologyRestriction X {x} isCompact_singleton n

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- On ordinary finite chains, compact restriction is exactly the standard
absolute-to-relative projection. -/
@[reassoc]
theorem ordinaryToLocallyFinite_comp_compactRestriction (X : TopCat.{0})
    (K : Set X) (hK : IsCompact K) :
    LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap ℤ X ≫ locallyFiniteCompactRestriction X K hK =
      LocalHomology.Cycles.relativeChainProjection X Kᶜ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change (LocalHomology.Cycles.relativeChainProjection X Kᶜ).f n
      (locallyFiniteCompactTruncation X K hK n (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite ℤ X n c)) =
    (LocalHomology.Cycles.relativeChainProjection X Kᶜ).f n c
  apply relativeChainProjection_eq_of_agrees_near
  intro σ hσ
  rw [locallyFiniteCompactTruncation_coefficients, ite_eq_left hσ]
  rfl

/-- The same compatibility for actual ordinary singular-homology classes. -/
@[reassoc]
theorem ordinaryToLocallyFinite_comp_compactHomologyRestriction (X : TopCat.{0})
    (K : Set X) (hK : IsCompact K) (n : ℕ) :
    HomologicalComplex.homologyMap (LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap ℤ X) n ≫
        locallyFiniteCompactHomologyRestriction X K hK n =
      HomologicalComplex.homologyMap (LocalHomology.Cycles.relativeChainProjection X Kᶜ) n := by
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun g => HomologicalComplex.homologyMap g n)
      (ordinaryToLocallyFinite_comp_compactRestriction X K hK)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Restricting first near L and then to the quotient near K agrees with
direct restriction whenever K is contained in L. -/
@[reassoc]
theorem locallyFiniteCompactRestriction_subset (X : TopCat.{0}) {K L : Set X}
    (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ L) :
    locallyFiniteCompactRestriction X L hL ≫
        LocalHomology.Cycles.relativeSingularChainsMap (𝟙 X) (A := Lᶜ) (B := Kᶜ)
          (fun _ hx hxK => hx (hKL hxK)) =
      locallyFiniteCompactRestriction X K hK := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  have hp :
      (LocalHomology.Cycles.relativeChainProjection X Lᶜ).f n ≫
          (LocalHomology.Cycles.relativeSingularChainsMap (𝟙 X) (A := Lᶜ) (B := Kᶜ)
            (fun _ hx hxK => hx (hKL hxK))).f n =
        (LocalHomology.Cycles.relativeChainProjection X Kᶜ).f n := by
    have h := LocalHomology.Cycles.relativeChainProjection_naturality (𝟙 X) (A := Lᶜ) (B := Kᶜ)
      (fun _ hx hxK => hx (hKL hxK))
    rw [LocalHomology.Cycles.integralSingularChainFunctor.map_id, Category.id_comp] at h
    simpa only [HomologicalComplex.comp_f] using HomologicalComplex.congr_hom h n
  change (LocalHomology.Cycles.relativeSingularChainsMap (𝟙 X) (A := Lᶜ) (B := Kᶜ)
      (fun _ hx hxK => hx (hKL hxK))).f n
      ((LocalHomology.Cycles.relativeChainProjection X Lᶜ).f n (locallyFiniteCompactTruncation X L hL n c)) =
    (LocalHomology.Cycles.relativeChainProjection X Kᶜ).f n (locallyFiniteCompactTruncation X K hK n c)
  calc
    _ = (LocalHomology.Cycles.relativeChainProjection X Kᶜ).f n (locallyFiniteCompactTruncation X L hL n c) :=
      ConcreteCategory.congr_hom hp (locallyFiniteCompactTruncation X L hL n c)
    _ = _ := by
      apply relativeChainProjection_eq_of_agrees_near
      intro σ hσ
      have hσL : (LocallyFiniteChains.Cycles.singularSimplexImage X n σ ∩ L).Nonempty := by
        obtain ⟨x, hx, hxK⟩ := hσ
        exact ⟨x, hx, hKL hxK⟩
      rw [locallyFiniteCompactTruncation_coefficients, ite_eq_left hσL,
        locallyFiniteCompactTruncation_coefficients, ite_eq_left hσ]

/-- Nested compact-support restrictions are compatible on homology. -/
@[reassoc]
theorem locallyFiniteCompactHomologyRestriction_subset (X : TopCat.{0}) {K L : Set X}
    (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ L) (n : ℕ) :
    locallyFiniteCompactHomologyRestriction X L hL n ≫
        LocalHomology.Cycles.relativeSingularHomologyMap (𝟙 X) (A := Lᶜ) (B := Kᶜ)
          (fun _ hx hxK => hx (hKL hxK)) n =
      locallyFiniteCompactHomologyRestriction X K hK n := by
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun g => HomologicalComplex.homologyMap g n)
      (locallyFiniteCompactRestriction_subset X hK hL hKL)

/-- In a compact ambient space, every compact restriction is the ordinary
absolute-to-relative projection after the canonical locally finite comparison. -/
theorem locallyFiniteCompactRestriction_eq_compactComparison
    (X : TopCat.{0}) [CompactSpace X] (K : Set X) (hK : IsCompact K) :
    locallyFiniteCompactRestriction X K hK =
      (LocallyFiniteComparison.Cycles.locallyFiniteOrdinaryChainIso ℤ X).hom ≫ LocalHomology.Cycles.relativeChainProjection X Kᶜ := by
  apply (cancel_epi (LocallyFiniteComparison.Cycles.ordinaryLocallyFiniteChainIso ℤ X).hom).1
  calc
    _ = LocalHomology.Cycles.relativeChainProjection X Kᶜ := by
      rw [LocallyFiniteComparison.Cycles.ordinaryLocallyFiniteChainIso_hom, ordinaryToLocallyFinite_comp_compactRestriction]
    _ = _ := by
      change LocalHomology.Cycles.relativeChainProjection X Kᶜ =
        (LocallyFiniteComparison.Cycles.ordinaryLocallyFiniteChainIso ℤ X).hom ≫
          ((LocallyFiniteComparison.Cycles.ordinaryLocallyFiniteChainIso ℤ X).inv ≫ LocalHomology.Cycles.relativeChainProjection X Kᶜ)
      exact ((LocallyFiniteComparison.Cycles.ordinaryLocallyFiniteChainIso ℤ X).hom_inv_id_assoc
        (LocalHomology.Cycles.relativeChainProjection X Kᶜ)).symm

/-- Compact ambient compatibility on actual homology. -/
theorem locallyFiniteCompactHomologyRestriction_eq_compactComparison
    (X : TopCat.{0}) [CompactSpace X] (K : Set X) (hK : IsCompact K) (n : ℕ) :
    locallyFiniteCompactHomologyRestriction X K hK n =
      (LocallyFiniteComparison.Cycles.locallyFiniteOrdinaryHomologyIso ℤ X n).hom ≫
        HomologicalComplex.homologyMap (LocalHomology.Cycles.relativeChainProjection X Kᶜ) n := by
  change HomologicalComplex.homologyMap (locallyFiniteCompactRestriction X K hK) n =
    HomologicalComplex.homologyMap (LocallyFiniteComparison.Cycles.locallyFiniteOrdinaryChainIso ℤ X).hom n ≫
      HomologicalComplex.homologyMap (LocalHomology.Cycles.relativeChainProjection X Kᶜ) n
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun g => HomologicalComplex.homologyMap g n)
      (locallyFiniteCompactRestriction_eq_compactComparison X K hK)

/-- Whole-space restriction, expressed using the empty-subspace relative complex. -/
def locallyFiniteWholeSpaceRelativeRestriction (X : TopCat.{0}) [CompactSpace X] :
    LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X ⟶ LocalHomology.Cycles.relativeSingularChains X ∅ :=
  locallyFiniteCompactRestriction X Set.univ isCompact_univ ≫
    LocalHomology.Cycles.relativeSingularChainsMap (𝟙 X) (A := Set.univᶜ) (B := ∅)
      (fun x hx => hx (Set.mem_univ x))

/-- After identifying C(X,∅) with C(X), whole-space compact restriction is
precisely the previously constructed inverse comparison. -/
theorem locallyFiniteWholeSpaceRestriction_eq_comparison
    (X : TopCat.{0}) [CompactSpace X] :
    locallyFiniteWholeSpaceRelativeRestriction X ≫ (Point.Cycles.relativeEmptyChainsIso X).hom =
      (LocallyFiniteComparison.Cycles.locallyFiniteOrdinaryChainIso ℤ X).hom := by
  have h : locallyFiniteWholeSpaceRelativeRestriction X =
      (LocallyFiniteComparison.Cycles.locallyFiniteOrdinaryChainIso ℤ X).hom ≫ LocalHomology.Cycles.relativeChainProjection X ∅ := by
    unfold locallyFiniteWholeSpaceRelativeRestriction
    rw [locallyFiniteCompactRestriction_eq_compactComparison, Category.assoc,
      LocalHomology.Cycles.relativeChainProjection_naturality, LocalHomology.Cycles.integralSingularChainFunctor.map_id,
      Category.id_comp]
  rw [h, Category.assoc]
  change (LocallyFiniteComparison.Cycles.locallyFiniteOrdinaryChainIso ℤ X).hom ≫
      ((Point.Cycles.relativeEmptyChainsIso X).inv ≫ (Point.Cycles.relativeEmptyChainsIso X).hom) =
    (LocallyFiniteComparison.Cycles.locallyFiniteOrdinaryChainIso ℤ X).hom
  rw [Iso.inv_hom_id, Category.comp_id]

/-- The whole-space restriction identity also holds on actual homology. -/
theorem locallyFiniteWholeSpaceHomologyRestriction_eq_comparison
    (X : TopCat.{0}) [CompactSpace X] (n : ℕ) :
    HomologicalComplex.homologyMap (locallyFiniteWholeSpaceRelativeRestriction X) n ≫
        (Point.Cycles.relativeEmptyHomologyIso X n).hom =
      (LocallyFiniteComparison.Cycles.locallyFiniteOrdinaryHomologyIso ℤ X n).hom := by
  change HomologicalComplex.homologyMap (locallyFiniteWholeSpaceRelativeRestriction X) n ≫
      HomologicalComplex.homologyMap (Point.Cycles.relativeEmptyChainsIso X).hom n =
    HomologicalComplex.homologyMap (LocallyFiniteComparison.Cycles.locallyFiniteOrdinaryChainIso ℤ X).hom n
  rw [← HomologicalComplex.homologyMap_comp,
    locallyFiniteWholeSpaceRestriction_eq_comparison]

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles
