import OAI.RepresentationTheory.Theta.Geometric.Rational.PeriodInverse
import OAI.RepresentationTheory.Theta.Geometric.Rational.PeriodCM
import OAI.RepresentationTheory.Theta.Geometric.Period.Models

/-! # Integral Rational Period Iso -/

namespace OAI.RepresentationTheory.Theta.Geometric.IntegralRationalPeriodIso

noncomputable section

/-! A rational SU matrix preserving the original integral lattice
induces an actual algebraic group isomorphism of its two period models. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

namespace ActiveHeckeThetaData

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (g : D.RationalSU)
    (hΛ : ∀ v, v ∈ D.pel.reference.lattice ↔ D.rationalLinear g v ∈ D.pel.reference.lattice)
    (x : D.domain)

include hg hΛ in
theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.rationalPeriodLinear_integral (v : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s))
    (hv : v ∈ D.periodLattice x.val) :
    D.rationalPeriodLinear g x v ∈ D.periodLattice (D.rationalPeriodPoint g x).val := by
  obtain ⟨u, hu, rfl⟩ := (D.periodLattice_mem x.val v).mp hv
  rw [D.rationalPeriodLinear_reference hg]
  exact (D.periodLattice_mem _ _).mpr ⟨_, (hΛ u).mp hu, rfl⟩

include hg hΛ in
theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.rationalPeriodLinear_inverse_integral (v : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s))
    (hv : v ∈ D.periodLattice (D.rationalPeriodPoint g x).val) :
    D.rationalPeriodLinear g⁻¹ (D.rationalPeriodPoint g x) v ∈ D.periodLattice x.val := by
  obtain ⟨u, hu, rfl⟩ := (D.periodLattice_mem (D.rationalPeriodPoint g x).val v).mp hv
  have hgu : D.rationalLinear g⁻¹ u ∈ D.pel.reference.lattice := by
    apply (hΛ (D.rationalLinear g⁻¹ u)).mpr
    rw [map_inv]
    change D.rationalLinear g ((D.rationalLinear g).symm u) ∈ _
    rw [LinearEquiv.apply_symm_apply]
    exact hu
  rw [D.rationalPeriodLinear_reference hg]
  change D.periodReferenceEmbedding (D.periodMap g⁻¹ (D.periodMap g x.val)) (D.rationalLinear g⁻¹ u) ∈ _
  rw [D.periodMap_inv_apply]
  exact (D.periodLattice_mem _ _).mpr ⟨_, hgu, rfl⟩

def _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.integralRationalTorusMap : (D.canonicalPeriodData hg x).periodTorus →+
    (D.canonicalPeriodData hg (D.rationalPeriodPoint g x)).periodTorus :=
  Torus.Hom.torusLinearMap (D.canonicalPeriodData hg x) (D.canonicalPeriodData hg (D.rationalPeriodPoint g x))
    (D.rationalPeriodLinear g x) (D.rationalPeriodLinear_integral hg g hΛ x)

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsProper A.toOver.hom := A.variety.presentation.projective.isProper

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.exists_integralRationalPeriodIso
    (M : D.PeriodModel hg x) (N : D.PeriodModel hg (D.rationalPeriodPoint g x)) :
    ∃ e : M.abelian.toOver ≅ N.abelian.toOver, IsMonHom e.hom ∧
      ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom (M.period t) = N.period (D.integralRationalTorusMap hg g hΛ x t) := by
  let Φ := D.canonicalPeriodData hg x
  let Ψ := D.canonicalPeriodData hg (D.rationalPeriodPoint g x)
  let u := D.rationalPeriodLinear g x
  let v := D.rationalPeriodLinear g⁻¹ (D.rationalPeriodPoint g x)
  let hu := D.rationalPeriodLinear_integral hg g hΛ x
  let hv := D.rationalPeriodLinear_inverse_integral hg g hΛ x
  obtain ⟨f, hf, hfp⟩ := Torus.Hom.exists_algebraic_torus_map Φ Ψ u hu M.abelian N.abelian
    M.period N.period M.period_add N.period_add
  obtain ⟨a, _, hap⟩ := Torus.Hom.exists_algebraic_torus_map Ψ Φ v hv N.abelian M.abelian
    N.period M.period N.period_add M.period_add
  have hfa : f ≫ a = 𝟙 M.abelian.toOver := by
    apply AlgebraicGeometry.Albanese.Construction.ClosedPoints.hom_ext_of_points
    intro p
    obtain ⟨t, rfl⟩ := M.period.surjective p
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t)) = M.period t
    rw [hfp, hap]
    apply congrArg M.period
    obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t
    exact congrArg (QuotientAddGroup.mk : Φ.space → Φ.periodTorus)
      (D.rationalPeriodLinear_inverse hg g x w)
  have haf : a ≫ f = 𝟙 N.abelian.toOver := by
    apply AlgebraicGeometry.Albanese.Construction.ClosedPoints.hom_ext_of_points
    intro p
    obtain ⟨t, rfl⟩ := N.period.surjective p
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a (N.period t)) = N.period t
    rw [hap, hfp]
    apply congrArg N.period
    obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t
    exact congrArg (QuotientAddGroup.mk : Ψ.space → Ψ.periodTorus)
      (D.rationalPeriodLinear_right_inverse hg g x w)
  exact ⟨⟨f, a, hfa, haf⟩, hf, hfp⟩

end ActiveHeckeThetaData

end

end OAI.RepresentationTheory.Theta.Geometric.IntegralRationalPeriodIso
