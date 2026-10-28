import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps

/-! # Faithfulness -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.Faithfulness.Abelian.IntrinsicPeriods

noncomputable section

/-!
Faithfulness of actual rational H¹ on algebraic group morphisms.
The proof constructs native linear lifts and computes their action on
the rational period lattice using the proved singular-period naturality.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.Geometry.ComplexTorus.BettiLattice.CM.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianComparison.Constructions
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicPeriodNaturality

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsProper A.toOver.hom :=
  A.variety.presentation.projective.isProper

/-- A lattice-preserving complex-linear map restricts to the rational
span of the actual integral period lattice. -/
def rationalLatticeMap {A B : Geometry.ComplexTorus.BettiLattice.CM.Construction.Torus} (L : A.V →ₗ[ℂ] B.V) (hL : Geometry.ComplexTorus.BettiLattice.CM.Construction.PreservesLattice L) :
    A.LQ →ₗ[ℚ] B.LQ :=
  ((L.restrictScalars ℚ).domRestrict A.LQ).codRestrict B.LQ (by
    rintro ⟨v, hv⟩
    change L v ∈ B.LQ
    induction hv using Submodule.span_induction with
    | mem v hv => exact Submodule.subset_span (hL v hv)
    | zero => simpa only [map_zero] using B.LQ.zero_mem
    | add v w _ _ hv hw => simpa only [map_add] using B.LQ.add_mem hv hw
    | smul q v _ hv =>
      change (L.restrictScalars ℚ) (q • v) ∈ B.LQ
      rw [map_smul]
      exact B.LQ.smul_mem q hv)

theorem rationalLatticeMap_apply {A B : Geometry.ComplexTorus.BettiLattice.CM.Construction.Torus} (L : A.V →ₗ[ℂ] B.V)
    (hL : Geometry.ComplexTorus.BettiLattice.CM.Construction.PreservesLattice L) (v : A.LQ) :
    (rationalLatticeMap L hL v : B.V) = L (v : A.V) := rfl

/-- The actual H¹ pullback is the transpose of the native rational
lattice map; no comparison formula is assumed for the algebraic map. -/
theorem rationalH1Equiv_algebraic_pullback {A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (f : A.toOver ⟶ B.toOver) [IsMonHom f]
    (L : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℂ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B)
    (hL : Geometry.ComplexTorus.BettiLattice.CM.Construction.PreservesLattice (A := IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A) (B := IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B) L)
    (hlift : Geometry.ComplexTorus.BettiLattice.CM.Construction.Lifts (IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraicTorusMap f) L) (c : B.variety.rationalCohomology 1) :
    AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianComparison.Constructions.rationalH1Equiv IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A (AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback f c) =
      (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianComparison.Constructions.rationalH1Equiv IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B c).comp
        (rationalLatticeMap (A := IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A) (B := IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B) L hL) := by
  have hp := AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicPeriodNaturality.rationalH1Equiv_nativeMap_pullback IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B A (IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraicTorusMap f)
    (IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraicTorusMap_holomorphic f) L
    (rationalLatticeMap (A := IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A) (B := IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B) L hL) hL hlift
    (fun _ => rfl) c
  have he :
      TopCat.ofHom ⟨AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.nativeMap IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B A (IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraicTorusMap f),
        (AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.nativeMap_mdifferentiable IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B A (IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraicTorusMap f)
          (IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraicTorusMap_holomorphic f)).continuous⟩ =
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f := by
    apply TopCat.ext
    exact IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.nativeMap_algebraicTorusMap f
  rw [he] at hp
  exact hp

/-- Algebraic group morphisms between actual abelian varieties are
determined by their pullbacks on the actual rational singular H¹. -/
theorem algebraic_group_map_eq_of_h1Pullback_eq {A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (f g : A.toOver ⟶ B.toOver) [IsMonHom f] [IsMonHom g]
    (hfg : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback f = AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback g) : f = g := by
  obtain ⟨L, ⟨hL, hlift⟩, _⟩ := IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraic_map_linear_lift f
  obtain ⟨M, ⟨hM, hmlift⟩, _⟩ := IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraic_map_linear_lift g
  have hQ : rationalLatticeMap (A := IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A) (B := IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B) L hL =
      rationalLatticeMap (A := IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A) (B := IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B) M hM := by
    apply LinearMap.ext
    intro v
    apply (Module.eval_apply_injective ℚ)
    apply LinearMap.ext
    intro φ
    obtain ⟨c, rfl⟩ := (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianComparison.Constructions.rationalH1Equiv IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B).surjective φ
    have hf := rationalH1Equiv_algebraic_pullback f L hL hlift c
    have hg := rationalH1Equiv_algebraic_pullback g M hM hmlift c
    rw [hfg] at hf
    exact LinearMap.congr_fun (hf.symm.trans hg) v
  have hLM : L = M := by
    apply Geometry.ComplexTorus.BettiLattice.CM.Construction.linear_ext_lq (A := IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A) (B := IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B)
    intro v
    exact congrArg (fun w : (IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B).LQ => (w : (IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B).V))
      (LinearMap.congr_fun hQ v)
  have htorus : IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraicTorusMap f = IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraicTorusMap g :=
    Geometry.ComplexTorus.BettiLattice.CM.Construction.lifts_group_unique hlift (hLM.symm ▸ hmlift)
  apply AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.schemeMap_ext
  intro x
  rw [← IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.nativeMap_algebraicTorusMap f, ← IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.nativeMap_algebraicTorusMap g, htorus]

end

end OAI.ArithmeticGeometry.Descent.CMVariety.Faithfulness.Abelian.IntrinsicPeriods
