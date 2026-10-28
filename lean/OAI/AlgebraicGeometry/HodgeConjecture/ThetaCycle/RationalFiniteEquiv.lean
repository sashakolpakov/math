import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalFiniteCoordinates
import OAI.RepresentationTheory.Theta.AdelicTopology
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular

/-! # Rational Finite Equiv -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalFiniteEquiv.CM

noncomputable section

/-! ThetaCycle: the two rational finite-adele models are isomorphic as
topological rings. Compact integral translates give the open-map argument. -/

open scoped Classical _root_.NumberField
open _root_.NumberField IsDedekindDomain Filter

def reindexedProductEquiv {I J : Type*} (A : I → Type*) (B : J → Type*)
    (e : I ≃ J) (f : ∀ j, A (e.symm j) ≃ B j) :
    ((i : I) → A i) ≃ ((j : J) → B j) :=
  (Equiv.piCongrLeft' A e).trans (Equiv.piCongrRight f)

theorem reindexed_product_equiv_apply {I J : Type*} (A : I → Type*) (B : J → Type*)
    (e : I ≃ J) (f : ∀ j, A (e.symm j) ≃ B j) (a : ∀ i, A i) (j : J) :
    reindexedProductEquiv A B e f a j = f j (a (e.symm j)) := rfl

theorem restricted_product_map_surjective {I J : Type*} (A : I → Type*) (B : J → Type*)
    (S : ∀ i, Set (A i)) (T : ∀ j, Set (B j))
    (e : I ≃ J) (f : ∀ j, A (e.symm j) ≃ B j)
    (m : RestrictedProduct A S cofinite → RestrictedProduct B T cofinite)
    (hm : ∀ a j, m a j = f j (a (e.symm j)))
    (hf : ∀ j x, f j x ∈ T j ↔ x ∈ S (e.symm j)) : Function.Surjective m := by
  intro a
  let x := (reindexedProductEquiv A B e f).symm a.val
  have he (j : J) : f j (x (e.symm j)) = a j := by
    rw [← reindexed_product_equiv_apply]
    exact congrFun ((reindexedProductEquiv A B e f).apply_symm_apply a.val) j
  have hx' : ∀ᶠ j in cofinite, x (e.symm j) ∈ S (e.symm j) := by
    filter_upwards [a.property] with j hj
    exact (hf j _).mp ((he j).symm ▸ hj)
  have hx : ∀ᶠ i in cofinite, x i ∈ S i := by
    have h := e.injective.tendsto_cofinite.eventually hx'
    filter_upwards [h] with i hi
    exact (congrArg (fun k => x k ∈ S k) (e.symm_apply_apply i)).mp hi
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  funext j
  exact (hm ⟨x, hx⟩ j).trans (he j)

def rationalFinitePiEquiv :
    ((v : HeightOneSpectrum (𝓞 ℚ)) → v.adicCompletion ℚ) ≃
      ((v : HeightOneSpectrum ℤ) → v.adicCompletion ℚ) :=
  reindexedProductEquiv _ _ RationalFiniteCoordinates.CM.rationalFinitePlaceEquiv
    (fun v => (RationalFiniteCoordinates.CM.rationalFiniteLocalEquiv v).toEquiv)

theorem rational_finite_pi_equiv_apply
    (a : (v : HeightOneSpectrum (𝓞 ℚ)) → v.adicCompletion ℚ) (v : HeightOneSpectrum ℤ) :
    rationalFinitePiEquiv a v = RationalFiniteCoordinates.CM.rationalFiniteLocalEquiv v (a (RationalFiniteCoordinates.CM.rationalFinitePlaceEquiv.symm v)) :=
  reindexed_product_equiv_apply _ _ _ _ a v

theorem rational_finite_adele_map_injective : Function.Injective RationalFiniteCoordinates.CM.rationalFiniteAdeleMap := by
  intro a b h
  have he : rationalFinitePiEquiv (fun v => a v) = rationalFinitePiEquiv (fun v => b v) := by
    funext v
    rw [rational_finite_pi_equiv_apply, rational_finite_pi_equiv_apply,
      ← RationalFiniteCoordinates.CM.rational_finite_adele_map_apply, ← RationalFiniteCoordinates.CM.rational_finite_adele_map_apply]
    exact congrArg (fun x : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => x v) h
  have hab := rationalFinitePiEquiv.injective he
  apply FiniteAdeleRing.ext
  intro v
  exact congrFun hab v

theorem rational_finite_adele_map_surjective : Function.Surjective RationalFiniteCoordinates.CM.rationalFiniteAdeleMap :=
  restricted_product_map_surjective _ _ _ _ RationalFiniteCoordinates.CM.rationalFinitePlaceEquiv
    (fun v => (RationalFiniteCoordinates.CM.rationalFiniteLocalEquiv v).toEquiv) RationalFiniteCoordinates.CM.rationalFiniteAdeleMap
    RationalFiniteCoordinates.CM.rational_finite_adele_map_apply RationalFiniteCoordinates.CM.rational_finite_local_integral

def rationalFiniteAdeleEquiv : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles ℚ ≃+* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf :=
  RingEquiv.ofBijective RationalFiniteCoordinates.CM.rationalFiniteAdeleMap
    ⟨rational_finite_adele_map_injective, rational_finite_adele_map_surjective⟩

theorem rational_field_finite_adeles_sigmaCompact : SigmaCompactSpace (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles ℚ) := by
  let C : ℚ → Set (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles ℚ) := fun q =>
    (fun x => algebraMap ℚ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles ℚ) q + x) '' (RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing ℚ : Set (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles ℚ))
  apply SigmaCompactSpace.of_countable (Set.range C) (Set.countable_range C)
  · rintro S ⟨q, rfl⟩
    exact (RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles.Construction.isCompact_finiteIntegralRing ℚ).image (continuous_const.add continuous_id)
  · apply Set.eq_univ_of_forall
    intro a
    obtain ⟨q, hq⟩ := RepresentationTheory.Weil.AdelicSplitting.CompactQuotient.Construction.exists_rational_finite_integral_remainder ℚ a
    apply Set.mem_sUnion.mpr
    refine ⟨C q, ⟨q, rfl⟩, ?_⟩
    exact ⟨a - algebraMap ℚ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles ℚ) q, hq, by abel_nf⟩

theorem rational_finite_adele_map_open : IsOpenMap RationalFiniteCoordinates.CM.rationalFiniteAdeleMap := by
  let : SigmaCompactSpace (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles ℚ) := rational_field_finite_adeles_sigmaCompact
  exact RationalFiniteCoordinates.CM.rationalFiniteAdeleMap.toAddMonoidHom.isOpenMap_of_sigmaCompact
    rational_finite_adele_map_surjective RationalFiniteCoordinates.CM.rational_finite_adele_map_continuous

def rationalFiniteAdeleHomeomorph : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles ℚ ≃ₜ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf :=
  rationalFiniteAdeleEquiv.toEquiv.toHomeomorphOfContinuousOpen
    RationalFiniteCoordinates.CM.rational_finite_adele_map_continuous rational_finite_adele_map_open

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalFiniteEquiv.CM
