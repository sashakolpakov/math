import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CupHomologyPairing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CupSpanning

/-! # Homology Pairing Antisymmetry -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyPairingAntisymmetry

noncomputable section

/-! The unnormalized degree-two homology pairing on an actual abelian
variety is already alternating. Degree-one cup generation proves this
for every original degree-two class. -/

open _root_.CategoryTheory

def nativeHomologyPairingLinear (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    A.variety.rationalCohomology 2 →ₗ[ℚ]
      HomologyCrossPairing.firstHomology (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) →ₗ[ℚ] HomologyCrossPairing.firstHomology (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) →ₗ[ℚ] ℚ :=
  (CrossClassEvaluation.crossClassPairing (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)).comp
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop A) 2).hom

theorem nativeHomologyPairingLinear_apply (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (c : A.variety.rationalCohomology 2) :
    nativeHomologyPairingLinear A c = HomologyCrossPairing.homologyClassPairing (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop A) c :=
  CrossClassEvaluation.crossClassPairing_multiplication (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop A) c

theorem homologyClassPairing_antisymm (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (c : A.variety.rationalCohomology 2)
    (x y : HomologyCrossPairing.firstHomology (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)) :
    HomologyCrossPairing.homologyClassPairing (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop A) c x y =
      -HomologyCrossPairing.homologyClassPairing (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop A) c y x := by
  let F : A.variety.rationalCohomology 2 →ₗ[ℚ] ℚ := {
    toFun d := nativeHomologyPairingLinear A d x y + nativeHomologyPairingLinear A d y x
    map_add' d e := by simp only [map_add, LinearMap.add_apply]; ring
    map_smul' r d := by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]; ring }
  have ht : F.ker = ⊤ := CupSpanning.abelianH2_cup_spanned A F.ker (fun a b => by
    change nativeHomologyPairingLinear A _ x y + nativeHomologyPairingLinear A _ y x = 0
    rw [nativeHomologyPairingLinear_apply, CupHomologyPairing.homologyClassPairing_cup, CupHomologyPairing.homologyClassPairing_cup]
    ring)
  have hc : F c = 0 := (show c ∈ F.ker from ht.symm ▸ Submodule.mem_top)
  change nativeHomologyPairingLinear A c x y + nativeHomologyPairingLinear A c y x = 0 at hc
  rw [nativeHomologyPairingLinear_apply] at hc
  exact eq_neg_of_add_eq_zero_left hc

theorem alternatingClassPairing_eq_original (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (c : A.variety.rationalCohomology 2) :
    HomologyCrossPairing.alternatingClassPairing (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop A) c =
      HomologyCrossPairing.homologyClassPairing (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop A) c := by
  ext x y
  change (1 / 2 : ℚ) * (HomologyCrossPairing.homologyClassPairing _ _ c x y - HomologyCrossPairing.homologyClassPairing _ _ c y x) = _
  rw [homologyClassPairing_antisymm A c y x]
  ring

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyPairingAntisymmetry
