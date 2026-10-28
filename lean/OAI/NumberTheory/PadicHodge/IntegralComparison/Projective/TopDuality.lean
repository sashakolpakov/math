import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.NegativePresentation

/-! # Top Duality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopDuality

noncomputable section

/-! Top-degree projective Serre duality for actual coherent sheaves,
obtained from the native residue trace and genuine negative-twist presentations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.DualityDescent OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

local instance (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

theorem pairing_bijective (n : ℕ) (hn : Fintype.card σ = n + 2)
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    Function.Bijective (Trace.DualityDescent.pairingMap (TopTracePairing.topFunctor (R := R) (σ := σ) n) (TopTracePairing.trace (R := R) n hn) M) := by
  classical
  let j := NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn
  let F := TopTracePairing.topFunctor (R := R) (σ := σ) n
  let τ := TopTracePairing.trace (R := R) n hn
  obtain ⟨P, hrows, hcolumns⟩ :=
    NegativePresentation.exists_presentation_above M j (n + 2)
  let rows := fun k : Fin P.rows => AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (P.rowDegree k)
  let columns := fun k : Fin P.columns => AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (P.columnDegree k)
  have hr : Function.Bijective (Trace.DualityDescent.pairingMap F τ (∐ rows)) :=
    Trace.DualityDescent.coproduct_bijective F τ rows (colimit.cocone (Discrete.functor rows))
      (colimit.isColimit (Discrete.functor rows))
      (fun k => TopTracePairing.negative_pairing_bijective_of_le n hn (P.rowDegree k) (hrows k))
  have hc : Function.Bijective (Trace.DualityDescent.pairingMap F τ (∐ columns)) :=
    Trace.DualityDescent.coproduct_bijective F τ columns (colimit.cocone (Discrete.functor columns))
      (colimit.isColimit (Discrete.functor columns))
      (fun k => TopTracePairing.negative_pairing_bijective_of_le n hn (P.columnDegree k) (hcolumns k))
  let S := ShortComplex.mk P.relations P.projection P.zero
  have : Epi S.g := P.epi
  have : (∐ rows).IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_quasicoherent j P.rowDegree
  have : Epi (F.map S.g) :=
    TopCechRightExact.map_epi (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R))
      (n + 1) (by simpa using hn.le) P.projection
  exact Trace.DualityDescent.cokernel_bijective F τ S P.exact hc.1 hr

def equivalence (n : ℕ) (hn : Fintype.card σ = n + 2)
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    (M ⟶ TopTracePairing.canonicalTwist (R := R) n hn) ≃
      ((TopTracePairing.topFunctor (R := R) (σ := σ) n).obj M ⟶
        ModuleCat.of Γ(Spec (CommRingCat.of R), ⊤) Γ(Spec (CommRingCat.of R), ⊤)) :=
  Equiv.ofBijective _ (pairing_bijective n hn M)

theorem equivalence_apply (n : ℕ) (hn : Fintype.card σ = n + 2)
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (f : M ⟶ TopTracePairing.canonicalTwist (R := R) n hn) :
    equivalence n hn M f = (TopTracePairing.topFunctor (R := R) (σ := σ) n).map f ≫ TopTracePairing.trace (R := R) n hn := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopDuality
