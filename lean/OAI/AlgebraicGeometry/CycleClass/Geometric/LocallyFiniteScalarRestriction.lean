import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteRestrictionNaturality
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains

/-! # Locally Finite Scalar Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteScalarRestriction

noncomputable section

/-!
# Scalar locally finite chains restricted near compact subsets

Only finitely many nonzero simplices of a spatially locally finite chain
meet a compact set. The actual finite truncation, followed by the actual
relative quotient, gives a scalar chain map. Its proper-map naturality is
proved from finite coefficient agreement near the compact inverse image.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cycles

variable (R : Type) [CommRing R]

/-- Actual ordinary scalar coefficients are pushed forward by the finite
sum along the map of genuine singular simplices. -/
theorem ordinaryScalarChainCoefficients_map {X Y : TopCat.{0}} (f : X ⟶ Y)
    (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X n) :
    LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R Y n (((RelativeScalarChains.Cycles.scalarSingularChainFunctor R).map f).f n c) =
      Finsupp.mapDomain ((TopCat.toSSet.map f).app (.op ⦋n⦌))
        (LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R X n c) := by
  have h : ((RelativeScalarChains.Cycles.scalarSingularChainFunctor R).map f).f n ≫
      ModuleCat.ofHom (LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R Y n).toLinearMap =
    ModuleCat.ofHom (LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R X n).toLinearMap ≫
      ModuleCat.ofHom (Finsupp.lmapDomain R R ((TopCat.toSSet.map f).app (.op ⦋n⦌))) := by
    apply (TopCat.toSSet.obj X).chainComplex_hom_ext
    intro σ
    change (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R) σ ≫
        (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)).f n ≫ _ = _
    rw [← Category.assoc, SSet.ι_chainComplexMap_f,
      LocallyFiniteComparison.Cycles.ordinarySingularChainCoefficients_simplex, ← Category.assoc,
      LocallyFiniteComparison.Cycles.ordinarySingularChainCoefficients_simplex]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change Finsupp.single ((TopCat.toSSet.map f).app (.op ⦋n⦌) σ) r =
      Finsupp.mapDomain ((TopCat.toSSet.map f).app (.op ⦋n⦌)) (Finsupp.single σ r)
    rw [Finsupp.mapDomain_single]
  exact ConcreteCategory.congr_hom h c

/-- Finite scalar chains supported in a subspace vanish in the genuine
relative scalar quotient. -/
theorem relativeScalarChainProjection_eq_zero_of_supported
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X n)
    (hc : ∀ σ, LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R X n c σ ≠ 0 →
      LocallyFiniteChains.Cycles.singularSimplexImage X n σ ⊆ A) :
    (RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n c = 0 := by
  let i := (TopCat.toSSet.map (LocalHomology.Cycles.subspaceInclusion X A)).app (.op ⦋n⦌)
  have hi : Function.Injective i := injective_of_mono i
  have hcoeff : LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R X n c ∈
      Set.range (Finsupp.mapDomain i) := by
    apply (Finsupp.mem_range_mapDomain_iff i hi _).2
    intro σ hσ
    by_contra hn
    apply hσ
    exact (SmallMayerVietoris.Cycles.mem_subspaceSingularSubcomplex X A (.op ⦋n⦌) σ).2 (hc σ hn)
  obtain ⟨b, hb⟩ := hcoeff
  let a := (LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R (TopCat.of A) n).symm b
  have ha : (RelativeScalarChains.Cycles.scalarSubspaceChainInclusion R X A).f n a = c := by
    apply (LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R X n).injective
    change LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R X n
      (((RelativeScalarChains.Cycles.scalarSingularChainFunctor R).map (LocalHomology.Cycles.subspaceInclusion X A)).f n a) = _
    rw [ordinaryScalarChainCoefficients_map]
    exact (congrArg (Finsupp.mapDomain i)
      ((LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R (TopCat.of A) n).apply_symm_apply b)).trans hb
  rw [← ha]
  exact ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (RelativeScalarChains.Cycles.scalarSubspaceChainInclusion_projection R X A) n) a

/-- The actual relative scalar quotient depends only on finite coefficients
of simplices that meet the retained subset. -/
theorem relativeScalarChainProjection_eq_of_agrees_near
    (X : TopCat.{0}) (K : Set X) (n : ℕ)
    (a b : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X n)
    (hab : ∀ σ, (LocallyFiniteChains.Cycles.singularSimplexImage X n σ ∩ K).Nonempty →
      LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R X n a σ =
        LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R X n b σ) :
    (RelativeScalarChains.Cycles.relativeScalarChainProjection R X Kᶜ).f n a =
      (RelativeScalarChains.Cycles.relativeScalarChainProjection R X Kᶜ).f n b := by
  apply sub_eq_zero.mp
  have hz := relativeScalarChainProjection_eq_zero_of_supported R X Kᶜ n (a - b) (by
    intro σ hσ x hx hxK
    apply hσ
    simp only [map_sub, Finsupp.sub_apply, sub_eq_zero]
    exact hab σ ⟨x, hx, hxK⟩)
  simpa only [map_sub] using hz

/-- The genuine finite scalar chain retaining exactly the simplices that
meet a compact set. -/
def locallyFiniteScalarCompactTruncation (X : TopCat.{0}) (K : Set X) (hK : IsCompact K)
    (n : ℕ) : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n →ₗ[R] (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X n :=
  (LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R X n).symm.toLinearMap.comp
    (LocallyFiniteCompactRestriction.Cycles.SpatialSupport.compactTruncation (LocallyFiniteChains.Cycles.singularSimplexImage X n) K hK)

@[simp]
theorem locallyFiniteScalarCompactTruncation_coefficients (X : TopCat.{0})
    (K : Set X) (hK : IsCompact K) (n : ℕ) (c : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n)
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌)) :
    LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R X n
        (locallyFiniteScalarCompactTruncation R X K hK n c) σ =
      if (LocallyFiniteChains.Cycles.singularSimplexImage X n σ ∩ K).Nonempty then c σ else 0 := by
  change (LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R X n)
      ((LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R X n).symm
        (LocallyFiniteCompactRestriction.Cycles.SpatialSupport.compactTruncation (LocallyFiniteChains.Cycles.singularSimplexImage X n) K hK c)) σ = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Scalar ordinary boundary coefficients agree with the boundary of their
actual locally finite inclusion. -/
theorem ordinaryScalarBoundary_coefficients (X : TopCat.{0}) (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X (n + 1))
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌)) :
    LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R X n
        ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).d (n + 1) n c) σ =
      LocallyFiniteChains.Cycles.locallyFiniteBoundary R X n (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X (n + 1) c) σ := by
  have h := congrArg ModuleCat.Hom.hom (LocallyFiniteComparison.Cycles.ordinaryToLocallyFinite_comm R X n)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex_d] at h
  have hc := LinearMap.congr_fun h c
  change LocallyFiniteChains.Cycles.locallyFiniteBoundary R X n (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X (n + 1) c) =
    LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X n ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).d (n + 1) n c) at hc
  exact congrArg (fun z : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n => z σ) hc.symm

/-- Truncating before taking the finite boundary preserves all boundary
coefficients whose simplex meets the compact subset. -/
theorem locallyFiniteScalarCompactTruncation_boundary_agrees (X : TopCat.{0})
    (K : Set X) (hK : IsCompact K) (n : ℕ) (c : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X (n + 1))
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌))
    (hσ : (LocallyFiniteChains.Cycles.singularSimplexImage X n σ ∩ K).Nonempty) :
    LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R X n
        ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).d (n + 1) n
          (locallyFiniteScalarCompactTruncation R X K hK (n + 1) c)) σ =
      LocallyFiniteChains.Cycles.locallyFiniteBoundary R X n c σ := by
  rw [ordinaryScalarBoundary_coefficients]
  apply LocallyFiniteCompactRestriction.Cycles.locallyFiniteBoundary_agrees_of_agrees X K n _ c _ σ hσ
  intro τ hτ
  change LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R X (n + 1)
    (locallyFiniteScalarCompactTruncation R X K hK (n + 1) c) τ = c τ
  rw [locallyFiniteScalarCompactTruncation_coefficients, ite_eq_left hτ]

/-- Finite compact truncation followed by the actual relative projection. -/
def locallyFiniteScalarCompactRestrictionDegree (X : TopCat.{0})
    (K : Set X) (hK : IsCompact K) (n : ℕ) :
    LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n →ₗ[R] (RelativeScalarChains.Cycles.relativeScalarChains R X Kᶜ).X n :=
  ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X Kᶜ).f n).hom.comp
    (locallyFiniteScalarCompactTruncation R X K hK n)

/-- Every actual finite representative agreeing near the compact set gives
the same relative scalar restriction. -/
theorem locallyFiniteScalarCompactRestrictionDegree_eq_of_agrees
    (X : TopCat.{0}) (K : Set X) (hK : IsCompact K) (n : ℕ)
    (c : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n) (a : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X n)
    (hca : ∀ σ, (LocallyFiniteChains.Cycles.singularSimplexImage X n σ ∩ K).Nonempty →
      c σ = LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R X n a σ) :
    locallyFiniteScalarCompactRestrictionDegree R X K hK n c =
      (RelativeScalarChains.Cycles.relativeScalarChainProjection R X Kᶜ).f n a := by
  change (RelativeScalarChains.Cycles.relativeScalarChainProjection R X Kᶜ).f n
    (locallyFiniteScalarCompactTruncation R X K hK n c) = _
  apply relativeScalarChainProjection_eq_of_agrees_near
  intro σ hσ
  rw [locallyFiniteScalarCompactTruncation_coefficients, ite_eq_left hσ]
  exact hca σ hσ

/-- The actual scalar compact restriction commutes with singular boundary. -/
theorem locallyFiniteScalarCompactRestriction_comm (X : TopCat.{0})
    (K : Set X) (hK : IsCompact K) (n : ℕ) :
    ModuleCat.ofHom (locallyFiniteScalarCompactRestrictionDegree R X K hK (n + 1)) ≫
        (RelativeScalarChains.Cycles.relativeScalarChains R X Kᶜ).d (n + 1) n =
      (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).d (n + 1) n ≫
        ModuleCat.ofHom (locallyFiniteScalarCompactRestrictionDegree R X K hK n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change ((RelativeScalarChains.Cycles.relativeScalarChains R X Kᶜ).d (n + 1) n).hom
      (((RelativeScalarChains.Cycles.relativeScalarChainProjection R X Kᶜ).f (n + 1)).hom
        (locallyFiniteScalarCompactTruncation R X K hK (n + 1) c)) =
    ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X Kᶜ).f n).hom
      (locallyFiniteScalarCompactTruncation R X K hK n
        (((LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).d (n + 1) n).hom c))
  rw [LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex_d]
  calc
    _ = (RelativeScalarChains.Cycles.relativeScalarChainProjection R X Kᶜ).f n
        ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).d (n + 1) n
          (locallyFiniteScalarCompactTruncation R X K hK (n + 1) c)) :=
      ConcreteCategory.congr_hom ((RelativeScalarChains.Cycles.relativeScalarChainProjection R X Kᶜ).comm (n + 1) n)
        (locallyFiniteScalarCompactTruncation R X K hK (n + 1) c)
    _ = _ := by
      apply relativeScalarChainProjection_eq_of_agrees_near
      intro σ hσ
      rw [locallyFiniteScalarCompactTruncation_boundary_agrees R X K hK n c σ hσ,
        locallyFiniteScalarCompactTruncation_coefficients, ite_eq_left hσ]
      rfl

/-- Compact relative restriction of the actual locally finite scalar complex. -/
def locallyFiniteScalarCompactRestriction (X : TopCat.{0}) (K : Set X) (hK : IsCompact K) :
    LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X ⟶ RelativeScalarChains.Cycles.relativeScalarChains R X Kᶜ where
  f n := ModuleCat.ofHom (locallyFiniteScalarCompactRestrictionDegree R X K hK n)
  comm' i j hij := by
    change j + 1 = i at hij
    subst i
    exact locallyFiniteScalarCompactRestriction_comm R X K hK j

/-- Compact restriction on actual scalar locally finite homology. -/
abbrev locallyFiniteScalarCompactHomologyRestriction
    (X : TopCat.{0}) (K : Set X) (hK : IsCompact K) (n : ℕ) :
    (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).homology n ⟶ RelativeScalarChains.Cycles.relativeScalarHomology R X Kᶜ n :=
  HomologicalComplex.homologyMap (locallyFiniteScalarCompactRestriction R X K hK) n

/-- The scalar extension reproduces the established integral restriction. -/
theorem locallyFiniteScalarCompactRestriction_int (X : TopCat.{0})
    (K : Set X) (hK : IsCompact K) :
    locallyFiniteScalarCompactRestriction ℤ X K hK = LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactRestriction X K hK := rfl

/-- For actual finite scalar chains, compact restriction is precisely the
ordinary absolute-to-relative projection. -/
@[reassoc]
theorem ordinaryToLocallyFinite_comp_scalarCompactRestriction
    (X : TopCat.{0}) (K : Set X) (hK : IsCompact K) :
    LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap R X ≫ locallyFiniteScalarCompactRestriction R X K hK =
      RelativeScalarChains.Cycles.relativeScalarChainProjection R X Kᶜ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change (RelativeScalarChains.Cycles.relativeScalarChainProjection R X Kᶜ).f n
      (locallyFiniteScalarCompactTruncation R X K hK n (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X n c)) =
    (RelativeScalarChains.Cycles.relativeScalarChainProjection R X Kᶜ).f n c
  apply relativeScalarChainProjection_eq_of_agrees_near
  intro σ hσ
  rw [locallyFiniteScalarCompactTruncation_coefficients, ite_eq_left hσ]
  rfl

/-- The finite-to-locally-finite homology comparison commutes with genuine
compact relative projection, with scalar coefficients. -/
@[reassoc]
theorem ordinaryToLocallyFinite_comp_scalarCompactHomologyRestriction
    (X : TopCat.{0}) (K : Set X) (hK : IsCompact K) (n : ℕ) :
    HomologicalComplex.homologyMap (LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap R X) n ≫
        locallyFiniteScalarCompactHomologyRestriction R X K hK n =
      HomologicalComplex.homologyMap (RelativeScalarChains.Cycles.relativeScalarChainProjection R X Kᶜ) n := by
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun g => HomologicalComplex.homologyMap g n)
      (ordinaryToLocallyFinite_comp_scalarCompactRestriction R X K hK)

variable {X Y : TopCat.{0}}

/-- Ordinary scalar pushforward has the same coefficients as the actual
proper locally finite pushforward of a finite chain. -/
theorem ordinaryScalarPushforward_coefficients (f : X ⟶ Y) (hf : IsProperMap f)
    (n : ℕ) (a : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X n)
    (τ : (TopCat.toSSet.obj Y).obj (.op ⦋n⦌)) :
    LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R Y n (((RelativeScalarChains.Cycles.scalarSingularChainFunctor R).map f).f n a) τ =
      LocallyFiniteProperMap.Cycles.locallyFiniteProperMap R f hf n (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X n a) τ := by
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (LocallyFiniteComparisonNaturality.Cycles.ordinaryToLocallyFiniteChainMap_naturality R f hf) n) a
  change LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R Y n (((RelativeScalarChains.Cycles.scalarSingularChainFunctor R).map f).f n a) =
    LocallyFiniteProperMap.Cycles.locallyFiniteProperMap R f hf n (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X n a) at h
  exact congrArg (fun z : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R Y n => z τ) h

/-- The proper push of the finite compact truncation agrees near the
retained compact set with the proper push of the whole locally finite chain. -/
theorem locallyFiniteScalarProperMap_truncation_agrees (f : X ⟶ Y) (hf : IsProperMap f)
    (K : Set Y) (hK : IsCompact K) (n : ℕ) (c : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n)
    (τ : (TopCat.toSSet.obj Y).obj (.op ⦋n⦌))
    (hτ : (LocallyFiniteChains.Cycles.singularSimplexImage Y n τ ∩ K).Nonempty) :
    LocallyFiniteProperMap.Cycles.locallyFiniteProperMap R f hf n c τ =
      LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R Y n
        (((RelativeScalarChains.Cycles.scalarSingularChainFunctor R).map f).f n
          (locallyFiniteScalarCompactTruncation R X (f ⁻¹' K)
            (hf.isCompact_preimage hK) n c)) τ := by
  rw [ordinaryScalarPushforward_coefficients R f hf]
  apply LocallyFiniteRestrictionNaturality.Cycles.locallyFiniteProperMap_agrees_of_agrees_near f hf K n c _ ?_ τ hτ
  intro σ hσ
  change c σ = LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R X n
    (locallyFiniteScalarCompactTruncation R X (f ⁻¹' K) (hf.isCompact_preimage hK) n c) σ
  rw [locallyFiniteScalarCompactTruncation_coefficients, ite_eq_left hσ]

/-- The exact finite-truncation formula for restricting a proper scalar
pushforward, before passing to cycles or homology. -/
theorem locallyFiniteScalarCompactRestrictionDegree_proper_truncation
    (f : X ⟶ Y) (hf : IsProperMap f) (K : Set Y) (hK : IsCompact K)
    (n : ℕ) (c : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n) :
    locallyFiniteScalarCompactRestrictionDegree R Y K hK n
        (LocallyFiniteProperMap.Cycles.locallyFiniteProperMap R f hf n c) =
      (RelativeScalarChains.Cycles.relativeScalarChainProjection R Y Kᶜ).f n
        (((RelativeScalarChains.Cycles.scalarSingularChainFunctor R).map f).f n
          (locallyFiniteScalarCompactTruncation R X (f ⁻¹' K)
            (hf.isCompact_preimage hK) n c)) := by
  apply locallyFiniteScalarCompactRestrictionDegree_eq_of_agrees
  intro τ hτ
  exact locallyFiniteScalarProperMap_truncation_agrees R f hf K hK n c τ hτ

/-- Proper scalar pushforward commutes with actual compact relative
restriction in each degree. -/
theorem locallyFiniteScalarCompactRestrictionDegree_naturality
    (f : X ⟶ Y) (hf : IsProperMap f) (K : Set Y) (hK : IsCompact K)
    (n : ℕ) (c : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n) :
    locallyFiniteScalarCompactRestrictionDegree R Y K hK n
        (LocallyFiniteProperMap.Cycles.locallyFiniteProperMap R f hf n c) =
      (RelativeScalarChains.Cycles.relativeScalarChainsMap R f (A := (f ⁻¹' K)ᶜ) (B := Kᶜ)
        (fun _ hx => hx)).f n
        (locallyFiniteScalarCompactRestrictionDegree R X (f ⁻¹' K)
          (hf.isCompact_preimage hK) n c) := by
  rw [locallyFiniteScalarCompactRestrictionDegree_proper_truncation]
  exact (ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom
      (RelativeScalarChains.Cycles.relativeScalarChainProjection_naturality R f (A := (f ⁻¹' K)ᶜ) (B := Kᶜ)
        (fun _ hx => hx)) n)
    (locallyFiniteScalarCompactTruncation R X (f ⁻¹' K) (hf.isCompact_preimage hK) n c)).symm

/-- The genuine proper-map square of scalar chain complexes. Properness
supplies the compactness of the retained inverse image. -/
@[reassoc]
theorem locallyFiniteScalarCompactRestriction_naturality
    (f : X ⟶ Y) (hf : IsProperMap f) (K : Set Y) (hK : IsCompact K) :
    LocallyFiniteProperMap.Cycles.locallyFiniteProperChainMap R f hf ≫ locallyFiniteScalarCompactRestriction R Y K hK =
      locallyFiniteScalarCompactRestriction R X (f ⁻¹' K) (hf.isCompact_preimage hK) ≫
        RelativeScalarChains.Cycles.relativeScalarChainsMap R f (A := (f ⁻¹' K)ᶜ) (B := Kᶜ) (fun _ hx => hx) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact locallyFiniteScalarCompactRestrictionDegree_naturality R f hf K hK n c

/-- The corresponding proper-map square on genuine scalar homology. -/
@[reassoc]
theorem locallyFiniteScalarCompactHomologyRestriction_naturality
    (f : X ⟶ Y) (hf : IsProperMap f) (K : Set Y) (hK : IsCompact K) (n : ℕ) :
    LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap R f hf n ≫
        locallyFiniteScalarCompactHomologyRestriction R Y K hK n =
      locallyFiniteScalarCompactHomologyRestriction R X (f ⁻¹' K)
          (hf.isCompact_preimage hK) n ≫
        HomologicalComplex.homologyMap
          (RelativeScalarChains.Cycles.relativeScalarChainsMap R f (A := (f ⁻¹' K)ᶜ) (B := Kᶜ) (fun _ hx => hx)) n := by
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun g => HomologicalComplex.homologyMap g n)
      (locallyFiniteScalarCompactRestriction_naturality R f hf K hK)

/-- Elementwise proper naturality for any actual scalar locally finite class. -/
theorem locallyFiniteScalarCompactHomologyRestriction_naturality_apply
    (f : X ⟶ Y) (hf : IsProperMap f) (K : Set Y) (hK : IsCompact K) (n : ℕ)
    (c : (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).homology n) :
    locallyFiniteScalarCompactHomologyRestriction R Y K hK n
        (LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap R f hf n c) =
      HomologicalComplex.homologyMap
        (RelativeScalarChains.Cycles.relativeScalarChainsMap R f (A := (f ⁻¹' K)ᶜ) (B := Kᶜ) (fun _ hx => hx)) n
        (locallyFiniteScalarCompactHomologyRestriction R X (f ⁻¹' K)
          (hf.isCompact_preimage hK) n c) :=
  ConcreteCategory.congr_hom
    (locallyFiniteScalarCompactHomologyRestriction_naturality R f hf K hK n) c

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteScalarRestriction
