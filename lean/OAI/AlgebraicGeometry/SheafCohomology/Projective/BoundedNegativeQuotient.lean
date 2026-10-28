import OAI.AlgebraicGeometry.SheafCohomology.Projective.FixedNegativeQuotient
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PairedTwistEquivalence
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PositiveTwistEquivalence

/-! # Bounded Negative Quotient -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.BoundedNegativeQuotient.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-! Negative-twist quotients with an arbitrarily prescribed lower bound on their exponents. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry MonoidalCategory
universe u
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance boundedNegativeQuotientMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Monoidal.Scheme.Modules.monoidalCategory X

def coordinateHyperplaneIdealModulePower_addIso (j : σ) :
    ∀ m n : ℕ,
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (m + n) ≅
        TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j m ⊗
          TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n
  | m, 0 => (ρ_ (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j m)).symm
  | m, n + 1 =>
      (coordinateHyperplaneIdealModulePower_addIso j m n ⊗ᵢ
        Iso.refl (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))) ≪≫
      α_ (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j m)
        (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n)
        (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))

theorem exists_fin_fixedCoordinateNegativeTwist_quotient_above [Fintype σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (j : σ) (B : ℕ) :
    ∃ (r : ℕ) (d : Fin r → ℕ)
      (f : (∐ fun k => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d k)) ⟶ M),
      (∀ k, B ≤ d k) ∧ Epi f := by
  let P := TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j B
  let T := M ⊗ P
  have : T.IsQuasicoherent := PositiveTwistEquivalence.MvPolynomial.moduleTensorCoordinateHyperplanePoleSheafPower_isQuasicoherent M j B
  have : T.IsFiniteType := PositiveTwistEquivalence.MvPolynomial.moduleTensorCoordinateHyperplanePoleSheafPower_isFiniteType M j B
  obtain ⟨r, d, f, hf⟩ := FixedNegativeQuotient.MvPolynomial.exists_fin_fixedCoordinateNegativeTwist_quotient T j
  have : Epi f := hf
  let E := PairedTwistEquivalence.MvPolynomial.coordinateHyperplaneTwistPairEquivalence (R := R) j B
  let L := fun k : Fin r => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d k)
  let e : (∐ fun k : Fin r => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d k + B)) ≅
      E.inverse.obj (∐ L) :=
    (Sigma.mapIso fun k => BoundedNegativeQuotient.MvPolynomial.coordinateHyperplaneIdealModulePower_addIso (R := R) j (d k) B) ≪≫
      (PreservesCoproduct.iso E.inverse L).symm
  let g : (∐ fun k : Fin r => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d k + B)) ⟶ M :=
    e.hom ≫ E.inverse.map f ≫ (E.unitIso.app M).inv
  refine ⟨r, fun k => d k + B, g, fun k => Nat.le_add_left B (d k), ?_⟩
  have : IsIso e.hom := e.isIso_hom
  have : Epi (E.inverse.map f) := E.inverse.map_epi f
  have : IsIso (E.unitIso.app M).inv := (E.unitIso.app M).isIso_inv
  dsimp only [g]
  exact @epi_comp _ _ _ _ _ e.hom (by infer_instance)
    (E.inverse.map f ≫ (E.unitIso.app M).inv)
      (@epi_comp _ _ _ _ _ (E.inverse.map f) (E.inverse.map_epi f)
        (E.unitIso.app M).inv
          (@IsIso.epi_of_iso _ _ _ _ (E.unitIso.app M).inv (E.unitIso.app M).isIso_inv))

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.BoundedNegativeQuotient.MvPolynomial
