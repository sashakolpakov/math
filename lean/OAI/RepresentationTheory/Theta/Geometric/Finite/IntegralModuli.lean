import OAI.RepresentationTheory.Theta.Geometric.Local.TraceB
import OAI.RepresentationTheory.Theta.Geometric.IntegralRationalModuli

/-! # Integral Moduli -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The exact finite subgroup from the public GeometricTheta statement preserves
the original reference lattice and fixes the actual reference moduli map.
The conjugate active coordinate follows from the original polarization. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hc : D.HasFiniteCoordinates)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)

include hg hc hgood hdegree in
theorem Data.ActiveHeckeThetaData.finiteIntegral_all_local (g : D.RationalSU)
    (hf : D.rationalFinite g ∈ (SphericalGU.Spherical.integralSL3 q).prod D.awayLevel.toSubgroup)
    (v : Fin s × Bool) : D.localMatrix v g ∈ SphericalGU.Spherical.integralSL3 q := by
  have hactive : D.activeLocal g ∈ SphericalGU.Spherical.integralSL3 q := hf.1
  have haway : D.away g ∈ D.awayLevel := hf.2
  by_cases hv : v.1 = D.pel.reference.distinguished
  · rcases v with ⟨v, b⟩
    change v = D.pel.reference.distinguished at hv
    subst v
    cases b
    · exact hactive
    · exact D.localMatrix_opposite_integral hg hc hgood hdegree g
        (D.pel.reference.distinguished, false) hactive
  · exact ((hc.2.2 g).mp haway).2 v hv

include hg hc hgood hdegree in
theorem Data.ActiveHeckeThetaData.finiteIntegral_preserves_reference_lattice (g : D.RationalSU)
    (hf : D.rationalFinite g ∈ (SphericalGU.Spherical.integralSL3 q).prod D.awayLevel.toSubgroup)
    (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    u ∈ D.pel.reference.lattice ↔ D.rationalLinear g u ∈ D.pel.reference.lattice :=
  D.rationalLinear_preserves_lattice_of_all_local hg hc hgood hdegree g
    (D.finiteIntegral_all_local hg hc hgood hdegree g hf) hf.2 u

include hc hgood hdegree in
theorem Data.ActiveHeckeThetaData.referenceModuliMap_finiteIntegral (g : D.RationalSU)
    (hf : D.rationalFinite g ∈ (SphericalGU.Spherical.integralSL3 q).prod D.awayLevel.toSubgroup)
    (x : D.domain) :
    D.referenceModuliMap hg x = D.referenceModuliMap hg (D.rationalPeriodPoint g x) :=
  Data.ActiveHeckeThetaData.referenceModuliMap_integralRational g
    (D.finiteIntegral_preserves_reference_lattice hg hc hgood hdegree g hf) hgood hc hf.2 x

end

end OAI.RepresentationTheory.Theta.Geometric
