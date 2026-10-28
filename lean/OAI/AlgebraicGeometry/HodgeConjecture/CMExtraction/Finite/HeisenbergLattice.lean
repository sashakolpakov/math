import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.BoundedScalar

/-! # Heisenberg Lattice -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.HeisenbergLattice.TestTransport

noncomputable section

/-! Concrete Heisenberg stabilizers of the finite lattice test. -/

open scoped Classical _root_.Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA)

theorem finite_heisenberg_lattice_fixed (r : ℚ) (hr : r ≠ 0)
    (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hp : p ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice r⁻¹ (inv_ne_zero hr))
    (hq : q ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice r hr)
    (hphase : D.finiteCharacter (-(∑ i, p i * (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (1 / 2) q) i)) = 1)
    (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter p q (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction r hr).val x =
      (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction r hr).val x := by
  have he : (∑ i, p i * (x i - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * q i)) =
      (∑ i, p i * x i) + (-(∑ i, p i * (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (1 / 2) q) i)) := by
    simp only [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale, mul_sub, Finset.sum_sub_distrib]
    exact sub_eq_add_neg _ _
  change D.finiteCharacter _ * (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction r hr).val (x - q) = _
  rw [he, D.finiteCharacter.map_add_eq_mul, hphase, mul_one,
    RepresentationTheory.Hecke.RadialDilation.FiniteHeisenberg.Realization.latticeTestFunction_translation r hr q hq]
  by_cases hx : x ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice r hr
  · rw [(RepresentationTheory.Hecke.RadialDilation.FiniteHeisenberg.Realization.finite_lattice_annihilator D r hr x).mp hx p hp, one_mul]
  · change _ * RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator r hr x = RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator r hr x
    rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator_of_notMem r hr hx, mul_zero]

theorem finite_heisenberg_lattice_fixed_half_translation (r : ℚ) (hr : r ≠ 0)
    (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hp : p ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice r⁻¹ (inv_ne_zero hr))
    (hq : q ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice r hr)
    (hhalf : RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (1 / 2) q ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice r hr) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter p q (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction r hr).val x =
      (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction r hr).val x :=
  finite_heisenberg_lattice_fixed D r hr p q hp hq
    (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteCharacter_pairing_dual_lattice D r hr hp hhalf) x

theorem finite_heisenberg_lattice_fixed_half_modulation (r : ℚ) (hr : r ≠ 0)
    (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hp : p ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice r⁻¹ (inv_ne_zero hr))
    (hq : q ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice r hr)
    (hhalf : RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (1 / 2) p ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice r⁻¹ (inv_ne_zero hr))
    (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter p q (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction r hr).val x =
      (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction r hr).val x := by
  apply finite_heisenberg_lattice_fixed D r hr p q hp hq _ x
  convert RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteCharacter_pairing_dual_lattice D r hr hhalf hq using 1
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale]
  ring

theorem finite_heisenberg_integral_coset (r : ℚ) (hr : r ≠ 0)
    (hL : (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := I) r hr : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) ⊆
      (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors (ι := I) : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)))
    (p q a : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hp : p ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors)
    (hhalf : RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (1 / 2) p ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors)
    (hq : q ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors) (hqa : q - a ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice r hr)
    (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter p q (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction r hr).val x =
      (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest r hr a).val x := by
  have hshift : (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction r hr).val (x - q) =
      (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction r hr).val (x - a) := by
    convert RepresentationTheory.Hecke.RadialDilation.FiniteHeisenberg.Realization.latticeTestFunction_translation r hr (q - a) hqa (x - a) using 1
    abel_nf
  change D.finiteCharacter _ * (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction r hr).val (x - q) =
    (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction r hr).val (x - a)
  rw [← hshift]
  by_cases hx : x - q ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice r hr
  · have hxi : x ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors := by
      have := RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors.add_mem (hL hx) hq
      simpa only [sub_add_cancel] using this
    have hphase : D.finiteCharacter
        (∑ i, p i * (x i - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * q i)) = 1 := by
      apply (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteCharacter_eq_one_iff D _).mpr
      apply RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.sum_mem
      intro i _
      have he : p i * (x i - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * q i) =
          p i * x i - (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (1 / 2) p) i * q i := by
        dsimp only [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale]
        ring
      rw [he]
      exact RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.sub_mem (RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.mul_mem (hp i) (hxi i))
        (RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.mul_mem (hhalf i) (hq i))
    rw [hphase, one_mul]
  · change _ * RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator r hr (x - q) = RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator r hr (x - q)
    rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator_of_notMem r hr hx, mul_zero]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.HeisenbergLattice.TestTransport
