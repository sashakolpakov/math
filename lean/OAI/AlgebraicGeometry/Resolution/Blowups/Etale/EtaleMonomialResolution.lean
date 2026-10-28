import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.MonomialLeaves
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.Monomial

/-! # Etale Monomial Resolution -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Uniform finite local monomial resolution certificates on étale affine ambient algebras. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {σ K : Type u} [Fintype σ] [DecidableEq σ] [Field K]

/-- The geometric and ideal-theoretic conditions for a selected monomial
step in an arbitrary étale ambient algebra, with its actual coefficient map. -/
def Etale.EtaleMonomialResolution.Construction.VerifiedEtaleMonomialNode (K S : Type u) [Field K] [CommRing S]
    [Algebra (MvPolynomial σ K) S] (a : σ → ℕ) (b : ℕ) (C : Finset σ) : Prop :=
  letI : Algebra K S := ((algebraMap (MvPolynomial σ K) S).comp MvPolynomial.C).toAlgebra
  let I := (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ K) S)
  Algebra.Smooth K (S ⧸ I) ∧ IsProper (ReesGrading.Construction.affineBlowupToSpec I) ∧
    Smooth (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial σ K) S)) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial σ K))) ∧
    ∀ i : C, (Blowups.Etale.MonomialStep.Construction.etaleSubsetCoordinateMap (R := K) (S := S) C i).Etale ∧
      ControlledTransform.Construction.blowupControlledTransform I
        ((Ideal.span {MonomialBlowupChart.Construction.coordinateMonomial a}).map (algebraMap (MvPolynomial σ K) S)) b
        ⟨algebraMap (MvPolynomial σ K) S (X i.val),
          Ideal.mem_map_of_mem _ (SubsetCoordinateBlowup.Construction.subsetCoordinateElement (R := K) C i).property⟩ =
        Ideal.span {Blowups.Etale.MonomialStep.Construction.etaleSubsetCoordinateMap (R := K) (S := S) C i
          (MonomialBlowupChart.Construction.coordinateMonomial (R := K) (MonomialTermination.Construction.monomialChartExponents a b C i.val))}

theorem Etale.EtaleMonomialResolution.Construction.verifiedEtaleMonomialNode (S : Type u) [CommRing S]
    [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]
    (a : σ → ℕ) (b : ℕ) (C : Finset σ) (hC : MonomialTermination.Construction.MinimalMonomialCenter a b C) :
    Blowups.Etale.EtaleMonomialResolution.Construction.VerifiedEtaleMonomialNode K S a b C := by
  let : Algebra K S := ((algebraMap (MvPolynomial σ K) S).comp MvPolynomial.C).toAlgebra
  let : IsScalarTower K (MvPolynomial σ K) S := IsScalarTower.of_algebraMap_eq' rfl
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing (MvPolynomial σ K) S
  exact ⟨Blowups.Etale.Monomial.Construction.etaleSubsetCoordinateCenter_smooth C, inferInstance, Blowups.Smooth.SubsetCoordinateBlowup.Construction.subsetCoordinateBlowup_smooth_of_etale C,
    fun i => ⟨Blowups.Etale.MonomialStep.Construction.etaleSubsetCoordinateMap_etale C i, Blowups.Etale.MonomialStep.Construction.etaleSubsetCoordinate_controlledIdeal a b C hC.2.1 i⟩⟩

/-- Every node and leaf is valid uniformly for étale ambient algebras.
Since each node provides étale coordinates on its actual child charts,
this predicate applies again to each resulting chart. -/
def MonomialTree.Construction.MonomialResolutionTree.VerifiedEtaleOver (K : Type u) [Field K]
    {b : ℕ} {a : σ → ℕ} : MonomialTree.Construction.MonomialResolutionTree b a → Prop
  | .done a _ => ∀ (S : Type u) [CommRing S] [Algebra (MvPolynomial σ K) S]
      [Algebra.Etale (MvPolynomial σ K) S] (q : Ideal S) [q.IsPrime],
      ¬ ((Ideal.span {MonomialBlowupChart.Construction.coordinateMonomial (R := K) a}).map (algebraMap (MvPolynomial σ K) S)).map
          (algebraMap S (Localization.AtPrime q)) ≤ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ b
  | .blowup a C _ children =>
      (∀ (S : Type u) [CommRing S] [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S],
        Blowups.Etale.EtaleMonomialResolution.Construction.VerifiedEtaleMonomialNode K S a b C) ∧ ∀ i : C, (children i).VerifiedEtaleOver K

variable [CharZero K]

theorem MonomialTree.Construction.MonomialResolutionTree.verifiedEtaleOver {b : ℕ} {a : σ → ℕ} (T : MonomialTree.Construction.MonomialResolutionTree b a) :
    T.VerifiedEtaleOver K := by
  induction T with
  | done a ha =>
    intro S _ _ _ q _
    exact Blowups.Etale.MonomialLeaves.Construction.etaleCoordinateMonomial_leaf_order a b ha q
  | blowup a C hC children ih =>
    refine ⟨?_, ih⟩
    intro S _ _ _
    exact Blowups.Etale.EtaleMonomialResolution.Construction.verifiedEtaleMonomialNode S a b C hC

/-- The same finite monomial tree resolves the control-order locus locally
in every étale ambient coordinate algebra, with actual smooth centers,
proper blowups, exact controlled transforms, and étale coordinates for the next step. -/
theorem Etale.EtaleMonomialResolution.Construction.exists_verified_etale_monomial_resolution (b : ℕ) (hb : 0 < b) (a : σ → ℕ) :
    ∃ T : MonomialTree.Construction.MonomialResolutionTree b a, T.height ≤ ∑ j, a j ∧ T.VerifiedEtaleOver K :=
  ⟨MonomialTree.Construction.monomialResolutionTree b hb a, MonomialTree.Construction.MonomialResolutionTree.height_le _,
    MonomialTree.Construction.MonomialResolutionTree.verifiedEtaleOver _⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
