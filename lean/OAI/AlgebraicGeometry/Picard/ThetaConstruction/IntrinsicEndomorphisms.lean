import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DefinitionsIntegral
import OAI.ArithmeticGeometry.Descent.CMVariety.MarkedPeriodClassification

/-! # Intrinsic Endomorphisms -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicEndomorphisms.Geometric

noncomputable section

/-!
ThetaConstruction for actual algebraic endomorphisms. The marking is a basis of the
kernel of the native exponential of the original abelian variety. The
comparison is proved using the unconditional algebraization theorem;
no comparison or endomorphism-existence assertion is a hypothesis.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.Geometry.ComplexTorus.BettiLattice.CM.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps
open scoped _root_.CategoryTheory.MonObj

open OAI.ArithmeticGeometry.Descent.CMVariety.MarkedPeriodClassification.Abelian.IntrinsicPeriods

variable {g : ℕ}

/-- The original algebraic group endomorphism realizes the integral
matrix on every complexified marked period vector. -/
def AlgebraicEndomorphismWithMatrix (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (DefinitionsIntegral.Index g) A) (M : DefinitionsIntegral.IntegralMatrix g) : Prop :=
  ∃ f : A.toOver ⟶ A.toOver, IsMonHom f ∧
    ∀ z : DefinitionsIntegral.CVec g,
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f
        (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A ((ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A).proj (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b z))) =
      HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A
        ((ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A).proj (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (DefinitionsIntegral.matrixAction M z)))

/-- A lattice-preserving linear map is algebraized on the original variety. -/
theorem algebraic_map_of_lattice_linear (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B)
    (hf : ∀ v ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A, f v ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B) :
    ∃ a : A.toOver ⟶ B.toOver, IsMonHom a ∧
      ∀ v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A,
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a
          (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A ((ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A).proj v)) =
        HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B ((ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B).proj (f v)) := by
  let F : (ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A).Point →+ (ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B).Point :=
    Geometry.ComplexTorus.BettiLattice.CM.Construction.descend (A := ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A) (B := ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B) f hf
  obtain ⟨a, ha, hap⟩ := ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A B (HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.nativeMap ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B A F)
    (HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.nativeMap_mdifferentiable ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B A F
      (Geometry.ComplexTorus.BettiLattice.CM.Construction.descend_holomorphic (A := ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A) (B := ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B) f hf))
  refine ⟨a, ha, fun v => ?_⟩
  rw [hap, HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.nativeMap_periodHomeomorph]
  rfl

/-- Actual algebraic endomorphisms occur exactly on their invariant period locus. -/
theorem algebraic_endomorphism_iff_period_invariant (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (DefinitionsIntegral.Index g) A) (M : DefinitionsIntegral.IntegralMatrix g) :
    AlgebraicEndomorphismWithMatrix A b M ↔
      ∀ z ∈ (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b).ker, DefinitionsIntegral.matrixAction M z ∈ (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b).ker := by
  constructor
  · rintro ⟨f, hf, hp⟩ z hz
    let : IsMonHom f := hf
    change ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (DefinitionsIntegral.matrixAction M z) = 0
    apply ArithmeticGeometry.Descent.CMVariety.MarkedPeriodClassification.Abelian.IntrinsicPeriods.zero_of_all_smul_mem_lattice A
    intro c
    have h := hp (c • z)
    have hzero : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (c • z) = 0 := by rw [map_smul, hz, smul_zero]
    rw [hzero] at h
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A 0) = _ at h
    rw [ArithmeticGeometry.Descent.CMVariety.MarkedPeriodClassification.Abelian.IntrinsicPeriods.native_zero] at h
    have hf1 : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f 1 = 1 := MonObj.one_comp f
    rw [hf1, ← ArithmeticGeometry.Descent.CMVariety.MarkedPeriodClassification.Abelian.IntrinsicPeriods.native_zero A] at h
    have he := (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A).injective h
    have hM : DefinitionsIntegral.matrixAction M (c • z) = c • DefinitionsIntegral.matrixAction M z := (DefinitionsIntegral.complexEnd M).map_smul c z
    change (0 : (ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A).Point) =
      (ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A).proj (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (DefinitionsIntegral.matrixAction M (c • z))) at he
    have hproj : (ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A).proj (c • ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (DefinitionsIntegral.matrixAction M z)) = 0 := by
      rw [hM, map_smul] at he
      exact he.symm
    exact ((ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A).proj_eq_zero _).mp hproj
  · intro h
    obtain ⟨f, hf⟩ := DefinitionsIntegral.exists_descended_map (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b) (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap_surjective b)
      ((ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b).comp (DefinitionsIntegral.complexEnd M)) h
    have hl : ∀ v ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A, f v ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A := by
      intro v hv
      have hv' : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (fun i => (b.repr ⟨v, hv⟩ i : ℂ)) = v :=
        ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap_repr b ⟨v, hv⟩
      rw [← hv', hf]
      change ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (DefinitionsIntegral.matrixAction M (fun i => (b.repr ⟨v, hv⟩ i : ℂ))) ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A
      have hm : DefinitionsIntegral.matrixAction M (fun i => (b.repr ⟨v, hv⟩ i : ℂ)) =
          fun i => ((∑ j, M i j * b.repr ⟨v, hv⟩ j : ℤ) : ℂ) := by
        ext i
        simp [DefinitionsIntegral.matrixAction]
      rw [hm]
      exact ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap_integer_mem b _
    obtain ⟨a, ha, hap⟩ := algebraic_map_of_lattice_linear A A f hl
    refine ⟨a, ha, fun z => ?_⟩
    rw [hap, hf]
    rfl

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicEndomorphisms.Geometric
