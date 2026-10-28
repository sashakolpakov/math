import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BlowupChart
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.PhaseLeaves
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Chart Open Base Change -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ChartOpenBaseChange.Construction

noncomputable section

/-! Point-preserving actual open base changes of arbitrary blowup charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

theorem blowupChartMap_isOpenImmersion (I : Ideal R) (a : I) (φ : R →+* S)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (ChartLift.Construction.blowupChartMap I φ a))) := by
  let : Algebra R S := φ.toAlgebra
  have h : Etale (Spec.map (CommRingCat.ofHom φ)) := inferInstance
  let : Algebra.Etale R S := RingHom.etale_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Etale)).mp h)
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (ChartFlatBaseChange.Construction.blowupChart_flat_isPullback (S := S) I a).flip inferInstance

/-- A point of a chart and a point over its base lift together through
the actual flat base-change square. No closed-point restriction is used. -/
theorem exists_blowupChartMap_prime (I : Ideal R) (a : I) (φ : R →+* S)
    (hφ : φ.Etale) (p : PrimeSpectrum (Charts.Construction.blowupChart I a)) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap φ q = PrimeSpectrum.comap (Charts.Construction.blowupChartConstants I a) p) :
    ∃ Q : PrimeSpectrum (Charts.Construction.blowupChart (I.map φ) ⟨φ a.val, Ideal.mem_map_of_mem _ a.property⟩),
      PrimeSpectrum.comap (ChartLift.Construction.blowupChartMap I φ a) Q = p ∧
        PrimeSpectrum.comap (Charts.Construction.blowupChartConstants (I.map φ)
          ⟨φ a.val, Ideal.mem_map_of_mem _ a.property⟩) Q = q := by
  let : Algebra R S := φ.toAlgebra
  let : Algebra.Etale R S := RingHom.etale_algebraMap.mp hφ
  exact Scheme.exists_preimage_of_isPullback (ChartFlatBaseChange.Construction.blowupChart_flat_isPullback (S := S) I a)
    p q hq.symm

variable (k : Type u) [CommRing k] [Algebra k R] [Algebra k S]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

def blowupChartMapAlgHom (I : Ideal R) (a : I) (φ : R →ₐ[k] S) :
    Charts.Construction.blowupChart I a →ₐ[k]
      Charts.Construction.blowupChart (I.map φ.toRingHom) ⟨φ a.val, Ideal.mem_map_of_mem _ a.property⟩ where
  toRingHom := ChartLift.Construction.blowupChartMap I φ.toRingHom a
  commutes' c := by
    change ChartLift.Construction.blowupChartMap I φ.toRingHom a (Charts.Construction.blowupChartConstants I a (algebraMap k R c)) =
      Charts.Construction.blowupChartConstants _ _ (algebraMap k S c)
    rw [ChartLift.Construction.blowupChartMap_constants]
    exact congrArg (Charts.Construction.blowupChartConstants _ _) (φ.commutes c)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ChartOpenBaseChange.Construction
