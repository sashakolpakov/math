import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalPurityNaturality
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeUniversalCoefficientNaturality

/-! # Homology Coordinates -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Local.HomologyCoordinates

noncomputable section

section

/-! Actual local homology maps of complex-linear coordinates, dual to the
established coordinate-independent local cohomology normalization. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.HomologicalComplex

namespace Constructions

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def complexLinearLocalChainsIso (e : E ≃L[ℂ] F) :
    Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of E) ({0}ᶜ : Set E) ≅
      Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of F) ({0}ᶜ : Set F) where
  hom := Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (Geometric.FiniteComplexLocalPurity.Cycles.complexLinearTopIso e).hom (Geometric.FiniteComplexLocalPurity.Cycles.complexLinearEquiv_mapsTo_puncture e)
  inv := Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (Geometric.FiniteComplexLocalPurity.Cycles.complexLinearTopIso e).inv (Geometric.FiniteComplexLocalPurity.Cycles.complexLinearEquiv_mapsTo_puncture e.symm)
  hom_inv_id := by
    rw [Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap_comp]
    simp only [Iso.hom_inv_id, Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap_id]
  inv_hom_id := by
    rw [Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap_comp]
    simp only [Iso.inv_hom_id, Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap_id]

def complexLinearLocalHomologyIso (e : E ≃L[ℂ] F) (n : ℕ) :
    Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of E) ({0}ᶜ : Set E) n ≅
      Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of F) ({0}ᶜ : Set F) n :=
  (homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).mapIso (complexLinearLocalChainsIso e)

@[simp]
theorem complexLinearLocalHomologyIso_hom (e : E ≃L[ℂ] F) (n : ℕ) :
    (complexLinearLocalHomologyIso e n).hom =
      homologyMap (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (Geometric.FiniteComplexLocalPurity.Cycles.complexLinearTopIso e).hom
        (Geometric.FiniteComplexLocalPurity.Cycles.complexLinearEquiv_mapsTo_puncture e)) n := rfl

def coordinateHomologyEquiv {p : ℕ} (e : E ≃L[ℂ] (Fin p → ℂ)) :
    Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of E) ({0}ᶜ : Set E) (2 * p) ≃ₗ[ℚ] ℚ :=
  (complexLinearLocalHomologyIso e (2 * p)).toLinearEquiv.trans
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyEquiv p)

theorem coordinateHomologyEquiv_eq_evaluation {p : ℕ} (e : E ≃L[ℂ] (Fin p → ℂ))
    (z : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of E) ({0}ᶜ : Set E) (2 * p)) :
    coordinateHomologyEquiv e z = Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ)
      (TopCat.of E) ({0}ᶜ : Set E) (2 * p) (Geometric.ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass e) z := by
  change Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyEquiv p
    (homologyMap (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (Geometric.FiniteComplexLocalPurity.Cycles.complexLinearTopIso e).hom
      (Geometric.FiniteComplexLocalPurity.Cycles.complexLinearEquiv_mapsTo_puncture e)) (2 * p) z) =
    Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of E) ({0}ᶜ : Set E) (2 * p)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Geometric.FiniteComplexLocalPurity.Cycles.complexLinearTopIso e).hom
        (Geometric.FiniteComplexLocalPurity.Cycles.complexLinearEquiv_mapsTo_puncture e) (2 * p) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)) z
  rw [Geometric.RelativeUniversalCoefficientNaturality.Cycles.relativeHomologyEvaluation_naturality]
  exact (congrArg (fun l => l
    (homologyMap (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (Geometric.FiniteComplexLocalPurity.Cycles.complexLinearTopIso e).hom
      (Geometric.FiniteComplexLocalPurity.Cycles.complexLinearEquiv_mapsTo_puncture e)) (2 * p) z))
        (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass_functional p)).symm

theorem coordinateHomologyEquiv_eq {p : ℕ} (e f : E ≃L[ℂ] (Fin p → ℂ)) :
    coordinateHomologyEquiv e = coordinateHomologyEquiv f := by
  ext z
  rw [coordinateHomologyEquiv_eq_evaluation, coordinateHomologyEquiv_eq_evaluation,
    Geometric.ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass_eq e f]

theorem coordinateHomologyEquiv_natural {p : ℕ} (e : E ≃L[ℂ] F)
    (cE : E ≃L[ℂ] (Fin p → ℂ)) (cF : F ≃L[ℂ] (Fin p → ℂ))
    (z : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of E) ({0}ᶜ : Set E) (2 * p)) :
    coordinateHomologyEquiv cF ((complexLinearLocalHomologyIso e (2 * p)).hom z) =
      coordinateHomologyEquiv cE z := by
  rw [coordinateHomologyEquiv_eq_evaluation, coordinateHomologyEquiv_eq_evaluation,
    complexLinearLocalHomologyIso_hom, ← Geometric.RelativeUniversalCoefficientNaturality.Cycles.relativeHomologyEvaluation_naturality]
  change Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of E) ({0}ᶜ : Set E) (2 * p)
    ((Geometric.FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso e (2 * p)).hom (Geometric.ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass cF)) z = _
  rw [Geometric.ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass_naturality e cE cF]

def coordinateHomologyGenerator {p : ℕ} (e : E ≃L[ℂ] (Fin p → ℂ)) :
    Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of E) ({0}ᶜ : Set E) (2 * p) :=
  (coordinateHomologyEquiv e).symm 1

@[simp]
theorem coordinateHomologyGenerator_normalization {p : ℕ} (e : E ≃L[ℂ] (Fin p → ℂ)) :
    coordinateHomologyEquiv e (coordinateHomologyGenerator e) = 1 :=
  (coordinateHomologyEquiv e).apply_symm_apply 1

theorem coordinateHomologyGenerator_natural {p : ℕ} (e : E ≃L[ℂ] F)
    (cE : E ≃L[ℂ] (Fin p → ℂ)) (cF : F ≃L[ℂ] (Fin p → ℂ)) :
    (complexLinearLocalHomologyIso e (2 * p)).hom (coordinateHomologyGenerator cE) =
      coordinateHomologyGenerator cF := by
  apply (coordinateHomologyEquiv cF).injective
  rw [coordinateHomologyEquiv_natural e cE cF,
    coordinateHomologyGenerator_normalization, coordinateHomologyGenerator_normalization]

end Constructions

end

/-! Local homology coordinates with explicit support and degree transports.
All maps retain the actual relative chain quotient of the displayed pair. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.HomologicalComplex
open OAI.AlgebraicGeometry.CycleClass.Thom.Local.HomologyCoordinates.Constructions

namespace Constructions.Pair

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def pairCoordinateHomologyEquiv {p : ℕ} (e : E ≃L[ℂ] (Fin p → ℂ))
    (A : Set E) (hA : A = {0}ᶜ) (n : ℕ) (hn : n = 2 * p) :
    Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of E) A n ≃ₗ[ℚ] ℚ :=
  (eqToIso (congrArg₂ (fun U j => Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of E) U j) hA hn)).toLinearEquiv.trans
    (coordinateHomologyEquiv e)

theorem pairCoordinateHomologyEquiv_apply {p : ℕ} (e : E ≃L[ℂ] (Fin p → ℂ))
    (A : Set E) (hA : A = {0}ᶜ) (n : ℕ) (hn : n = 2 * p)
    (z : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of E) A n) :
    pairCoordinateHomologyEquiv e A hA n hn z = coordinateHomologyEquiv e
      (eqToHom (congrArg (fun j => Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of E) ({0}ᶜ) j) hn)
        (eqToHom (congrArg (fun U => Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of E) U n) hA) z)) := by
  subst A
  subst n
  rfl

theorem pairCoordinateHomologyEquiv_degreeMap {p : ℕ} (e : E ≃L[ℂ] (Fin p → ℂ))
    (A : Set E) (hA : A = {0}ᶜ) (n m : ℕ) (hn : n = 2 * p) (hm : m = 2 * p)
    (hnm : n = m) (z : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of E) A n) :
    pairCoordinateHomologyEquiv e A hA m hm
      (eqToHom (congrArg (fun j => Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of E) A j) hnm) z) =
        pairCoordinateHomologyEquiv e A hA n hn z := by
  subst hnm
  rfl

theorem pairCoordinateHomologyEquiv_natural {p : ℕ} (e : E ≃L[ℂ] F)
    (cE : E ≃L[ℂ] (Fin p → ℂ)) (cF : F ≃L[ℂ] (Fin p → ℂ))
    (A : Set E) (B : Set F) (hA : A = {0}ᶜ) (hB : B = {0}ᶜ)
    (n : ℕ) (hn : n = 2 * p) (hf : Set.MapsTo (Geometric.FiniteComplexLocalPurity.Cycles.complexLinearTopIso e).hom A B)
    (z : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of E) A n) :
    pairCoordinateHomologyEquiv cF B hB n hn
      (homologyMap (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (Geometric.FiniteComplexLocalPurity.Cycles.complexLinearTopIso e).hom hf) n z) =
        pairCoordinateHomologyEquiv cE A hA n hn z := by
  subst A
  subst B
  subst n
  exact coordinateHomologyEquiv_natural e cE cF z

theorem pairCoordinateHomologyEquiv_coordinates {p : ℕ} (e f : E ≃L[ℂ] (Fin p → ℂ))
    (A : Set E) (hA : A = {0}ᶜ) (n : ℕ) (hn : n = 2 * p) :
    pairCoordinateHomologyEquiv e A hA n hn = pairCoordinateHomologyEquiv f A hA n hn := by
  subst A
  subst n
  exact coordinateHomologyEquiv_eq e f

theorem pairCoordinateHomologyEquiv_changeDimension {p q : ℕ} (hpq : p = q)
    (e : E ≃L[ℂ] (Fin p → ℂ)) (f : E ≃L[ℂ] (Fin q → ℂ))
    (A : Set E) (hA : A = {0}ᶜ) (n : ℕ) (hn : n = 2 * p) (hn' : n = 2 * q) :
    pairCoordinateHomologyEquiv e A hA n hn = pairCoordinateHomologyEquiv f A hA n hn' := by
  subst q
  exact pairCoordinateHomologyEquiv_coordinates e f A hA n hn

theorem coordinateHomologyEquiv_refl (p : ℕ)
    (z : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of (Fin p → ℂ)) ({0}ᶜ) (2 * p)) :
    coordinateHomologyEquiv (ContinuousLinearEquiv.refl ℂ (Fin p → ℂ)) z =
      Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyEquiv p z := by
  change Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyEquiv p
    (homologyMap (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (𝟙 (TopCat.of (Fin p → ℂ)))
      (A := {0}ᶜ) (B := {0}ᶜ) (fun _ hx => hx)) (2 * p) z) = _
  rw [Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap_id, homologyMap_id]
  rfl

theorem pairCoordinateHomologyEquiv_standard (p : ℕ) :
    pairCoordinateHomologyEquiv (ContinuousLinearEquiv.refl ℂ (Fin p → ℂ)) ({0}ᶜ) rfl (2 * p) rfl
      (Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator p) = 1 :=
  (coordinateHomologyEquiv_refl p (Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator p)).trans
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator_normalization p)

end Constructions.Pair

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Local.HomologyCoordinates
