import OAI.AlgebraicGeometry.ComplexPoints.AffineDensity
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineOpenSmooth
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeAffineCover
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeImmersionPointTopology
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Irreducible

/-! # Analytic Open Density -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnalyticOpenDensity

noncomputable section

/-! A nonempty open set in the actual analytic points of a smooth
integral complex scheme is Zariski dense. The argument uses density of
affine principal opens, with the original section-algebra characters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set OAI.AlgebraicGeometry.Foundations.Scheme.AffineOpenSmooth

theorem finiteTypeDomain_ideal_eq_bot_of_open_characters
    {A : Type*} [CommRing A] [Algebra ℂ A] [IsDomain A] [Algebra.FiniteType ℂ A]
    (I : Ideal A) (U : Set (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)) (hU : IsOpen U) (hUn : U.Nonempty)
    (hvan : ∀ x ∈ U, ∀ a ∈ I, x a = 0) : I = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  change a = 0
  by_contra hane
  obtain ⟨x, hx⟩ := hUn
  have hd := ComplexPoints.AffineDensity.ClosednessConstruction.dense_affine_principal_open a hane
  obtain ⟨y, hy, hya⟩ := mem_closure_iff.mp (hd x) U hU hx
  exact hya (hvan y hy a ha)

theorem smoothIntegral_closed_eq_univ_of_analytic_open
    (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hU : IsOpen U) (hUn : U.Nonempty)
    (C : Set X.left) (hC : IsClosed C)
    (hUC : ∀ x ∈ U, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ C) : C = univ := by
  obtain ⟨x, hx⟩ := hUn
  obtain ⟨V, hV, ψ, hψ⟩ := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineOpenPoint_lift X x
  have hxV : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ V := by
    have hr : x ∈ range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X V hV) := ⟨ψ, hψ⟩
    rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap] at hr
    exact hr
  let : Nonempty V := ⟨⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x, hxV⟩⟩
  let A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V
  let : IsDomain A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_isDomain X V
  let : Algebra.Smooth ℂ A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_smooth X V hV
  let g : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X V hV
  let f : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X :=
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X V hV
  let S : Set (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) := f ⁻¹' U
  have hS : IsOpen S := hU.preimage
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_affineOpenPointMap X V hV).continuous
  have hSn : S.Nonempty := by
    refine ⟨ψ, ?_⟩
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X V hV ψ ∈ U
    rwa [hψ]
  let C' : Set (PrimeSpectrum A) := g.left ⁻¹' C
  have hC' : IsClosed C' := hC.preimage g.left.continuous
  let I : Ideal A := PrimeSpectrum.vanishingIdeal C'
  have hI : I = ⊥ := by
    apply finiteTypeDomain_ideal_eq_bot_of_open_characters I S hS hSn
    intro χ hχ a ha
    have hpoint : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum χ ∈ C' := by
      have h := hUC (f χ) hχ
      change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A g χ) ∈ C at h
      rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying_affinePointMap] at h
      exact h
    change a ∈ (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum χ).asIdeal
    exact (PrimeSpectrum.mem_vanishingIdeal C' a).mp ha _ hpoint
  have hC'eq : C' = univ := by
    calc
      C' = closure C' := hC'.closure_eq.symm
      _ = PrimeSpectrum.zeroLocus (I : Set A) :=
        (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure C').symm
      _ = univ := by rw [hI]; exact PrimeSpectrum.zeroLocus_bot
  have hVC : (V : Set X.left) ⊆ C := by
    intro y hy
    have hr : y ∈ range g.left := by
      change y ∈ range hV.fromSpec
      rw [hV.range_fromSpec]
      exact hy
    obtain ⟨p, rfl⟩ := hr
    have hp : p ∈ C' := by rw [hC'eq]; trivial
    exact hp
  apply Set.eq_univ_of_forall
  intro y
  exact (closure_minimal hVC hC) ((V.isOpen.dense ⟨_, hxV⟩) y)

theorem analytic_open_eq_univ_of_closed_image
    {X Y Z : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    (f : X ⟶ Y) [IsImmersion f.left]
    (j : Z ⟶ Y) [IsClosedImmersion j.left]
    (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hU : IsOpen U) (hUn : U.Nonempty)
    (himage : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f '' U = range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j)) :
    U = univ := by
  let C : Set X.left := f.left ⁻¹' range j.left
  have hC : IsClosed C := j.left.isClosedEmbedding.isClosed_range.preimage f.left.continuous
  have hUC : ∀ x ∈ U, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ C := by
    intro x hx
    have h : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x ∈ range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j) :=
      himage ▸ ⟨x, hx, rfl⟩
    rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion j] at h
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x) ∈ range j.left at h
    rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying_map] at h
    exact h
  have hCall : C = univ := smoothIntegral_closed_eq_univ_of_analytic_open X U hU hUn C hC hUC
  apply Set.eq_univ_of_forall
  intro x
  have hxC : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ C := by rw [hCall]; trivial
  have hxj : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x ∈ range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j) := by
    rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion j]
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x) ∈ range j.left
    rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying_map]
    exact hxC
  rw [← himage] at hxj
  obtain ⟨y, hy, he⟩ := hxj
  have hxy : y = x := (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion f).injective he
  exact hxy ▸ hy

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnalyticOpenDensity
