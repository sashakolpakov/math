import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PELFiniteGroup
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LatticeTopology
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PrincipalLatticeDivision

/-! # Principal -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.Principal.CM

noncomputable section

/-! Principal membership of the actual rational source matrix is
detected by its PEL finite image and the original completed lattice. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hb : P.b = B.b)
  {J : Type*} [Fintype J] [DecidableEq J] [Submodule.IsLattice ℚ P.lattice]
  (b : Module.Basis J ℤ P.lattice)

include b in
omit [NumberField.IsCMField ↥E] in
theorem rational_mem (x : Fin 3 → E) :
    AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x ∈ P.completedLattice ↔ x ∈ P.lattice := by
  rw [show P.completedLattice = CMExtraction.LatticeCoordinates.TestTransport.completedVectorLattice E P.lattice from rfl,
    CMExtraction.LatticeCoordinates.TestTransport.completedVectorLattice_coordinates E P.lattice b,
    CMExtraction.LatticeCoordinates.TestTransport.lattice_mem_iff_integer_coordinates P.lattice b]
  rw [show AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x = (fun i => AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E (x i)) from rfl,
    CMExtraction.CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates_rational]
  exact forall_congr' (fun j => RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.rational_integral_iff ((b.extendOfIsLattice ℚ).equivFun x j))

def embedding : (Fin 3 → E) →ₗ[ℚ] (Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) :=
  LinearMap.pi (fun i => (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E).toLinearMap.comp (LinearMap.proj i))

include b in
theorem rational_principal (N : ℕ) (hN : 0 < N) (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (hg : Source.PELFiniteGroup.CM.pel E Q P hb (Source.RationalLocal.CM.finiteHom E Q g) ∈
      P.adelicPrincipalLevel N) :
    (Matrix.SpecialLinearGroup.toLin' g.val).restrictScalars ℚ ∈
      AbelianModuli.ReferenceFamily.Groups.principalLatticeSubgroup P.lattice.toAddSubgroup N := by
  let G := Source.PELFiniteGroup.CM.pel E Q P hb (Source.RationalLocal.CM.finiteHom E Q g)
  have hv (x : Fin 3 → E) : G.val (embedding E x) = embedding E (g.val.val *ᵥ x) :=
    Source.PELFiniteGroup.CM.Matrix.rational_vector E Q P hb g x
  change (∀ x, x ∈ P.completedLattice ↔ G.val x ∈ P.completedLattice) ∧
    (∀ x ∈ P.completedLattice, ∃ y ∈ P.completedLattice, G.val x - x = N • y) at hg
  change (∀ x, x ∈ P.lattice ↔ g.val.val *ᵥ x ∈ P.lattice) ∧
    (∀ x ∈ P.lattice, ∃ y ∈ P.lattice, g.val.val *ᵥ x - x = N • y)
  constructor
  · intro x
    exact (rational_mem E P b x).symm.trans
      ((hg.1 (embedding E x)).trans
        ((Iff.of_eq (congrArg (fun y => y ∈ P.completedLattice) (hv x))).trans
          (rational_mem E P b (g.val.val *ᵥ x))))
  · intro x hx
    have hx' := (rational_mem E P b x).mpr hx
    have hd := (CMExtraction.PrincipalLatticeDivision.TestTransport.lattice_multiple_iff_division P.completedLattice.toAddSubgroup N hN _).mp
      (hg.2 (embedding E x) hx')
    rw [hv, ← map_sub, ← map_smul] at hd
    have hd' := (rational_mem E P b ((N : ℚ)⁻¹ • (g.val.val *ᵥ x - x))).mp hd
    exact (CMExtraction.PrincipalLatticeDivision.TestTransport.lattice_multiple_iff_division P.lattice.toAddSubgroup N hN _).mpr hd'

include b in
theorem source_principal (hL : P.lattice = B.lattice) (N : ℕ) (hN : 0 < N)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (hg : Source.PELFiniteGroup.CM.pel E Q P hb (Source.RationalLocal.CM.finiteHom E Q g) ∈
      P.adelicPrincipalLevel N) :
    B.principalLevel N (Matrix.SpecialLinearGroup.toLin' g.val) := by
  have h := rational_principal E Q P hb b N hN g hg
  rw [hL] at h
  refine ⟨g.property, ?_, h.1, ?_⟩
  · rw [← LinearMap.det_toMatrix']
    erw [LinearMap.toMatrix'_toLin']
    exact g.val.property
  · intro x hx
    obtain ⟨y, hy, he⟩ := h.2 x hx
    exact ⟨y, hy, he.trans (Nat.cast_smul_eq_nsmul ℤ N y).symm⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.Principal.CM
