import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveMaps

/-! # Intrinsic Hodge Maps -/

namespace OAI

noncomputable section

namespace ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian

/-!
Algebraize rational Hodge maps when the canonical Hodge structures are
already supplied, as they are by the CMAbelianVariety CM hypothesis. This uses the
proved HolomorphicAlgebraicity algebraization theorem. It does not require Construction/HodgeComparison existence
inputs or a postulated weight-one algebraicity principle.

The proof follows the actual lattice-period construction of WeightOne,
with its two canonical-Hodge-structure existence calls replaced by the
given canonical structures.
-/

open _root_.CategoryTheory
open scoped TensorProduct _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.CM
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions OAI.Geometry.ComplexTorus.BettiLattice.CM.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianComparison.Constructions
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TorusModel.Constructions
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicPeriodNaturality

local instance (A : OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : AlgebraicGeometry.IsIntegral A.toOver.left :=
  A.variety.property
local instance (A : OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : AlgebraicGeometry.Smooth A.toOver.hom :=
  A.variety.presentation.smooth

/-- A rational map of the given canonical weight-one Hodge structures is
an actual algebraic group pullback after multiplication by a positive integer. -/
theorem hodge_map_algebraic_of_canonicalH1
    (A B : OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (HA : OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
    (HB : OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (B.variety.rationalCohomology 1))
    (hHA : OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.IsCanonicalH1 A.variety HA) (hHB : OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.IsCanonicalH1 B.variety HB)
    (u : A.variety.rationalCohomology 1 →ₗ[ℚ] B.variety.rationalCohomology 1)
    (hu : OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap HA HB u) :
    ∃ n : ℕ, 0 < n ∧ ∃ g : B.toOver ⟶ A.toOver,
      IsMonHom g ∧ OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback g = (n : ℚ) • u := by
  let hHolomorphicAlgebraicity : OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.HolomorphicAlgebraicityInput := OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.CM.holomorphic_group_hom_is_algebraic
  let eA := OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianComparison.Constructions.rationalH1Equiv hHolomorphicAlgebraicity A
  let eB := OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianComparison.Constructions.rationalH1Equiv hHolomorphicAlgebraicity B
  let uL : (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity A).H1Q →ₗ[ℚ] (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity B).H1Q :=
    eB.toLinearMap.comp (u.comp eA.symm.toLinearMap)
  have he : eB.symm.toLinearMap.comp uL = u.comp eA.symm.toLinearMap := by
    ext c
    exact eB.symm_apply_apply (u (eA.symm c))
  have heC (x : OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity A).H1Q) :
      eB.symm.toLinearMap.baseChange ℂ (uL.baseChange ℂ x) =
        u.baseChange ℂ (eA.symm.toLinearMap.baseChange ℂ x) := by
    calc
      _ = (eB.symm.toLinearMap.comp uL).baseChange ℂ x :=
        (LinearMap.congr_fun (LinearMap.baseChange_comp (A := ℂ)
          (f := uL) eB.symm.toLinearMap) x).symm
      _ = (u.comp eA.symm.toLinearMap).baseChange ℂ x :=
        congrArg (fun f => f.baseChange ℂ x) he
      _ = _ := LinearMap.congr_fun (LinearMap.baseChange_comp (A := ℂ)
        (f := eA.symm.toLinearMap) u) x
  have huL : OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TorusModel.Constructions.abelianH1Model hHolomorphicAlgebraicity A HA hHA).hodge
      (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TorusModel.Constructions.abelianH1Model hHolomorphicAlgebraicity B HB hHB).hodge uL := by
    intro x hx
    change eA.symm.toLinearMap.baseChange ℂ x ∈ HA.holomorphic at hx
    change eB.symm.toLinearMap.baseChange ℂ (uL.baseChange ℂ x) ∈ HB.holomorphic
    rw [heC]
    exact hu _ hx
  obtain ⟨n, hn, g, ⟨hg, f, fQ, hf, hlift, hfQ, hpull⟩, _⟩ :=
    (Geometry.ComplexTorus.BettiLattice.CM.Construction.rational_hodge_description (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity B) (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TorusModel.Constructions.abelianTorus hHolomorphicAlgebraicity A)
      (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TorusModel.Constructions.abelianH1Model hHolomorphicAlgebraicity B HB hHB) (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TorusModel.Constructions.abelianH1Model hHolomorphicAlgebraicity A HA hHA) uL).mp huL
  obtain ⟨a, ha, hapull⟩ := OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.holomorphic_h1_algebraicity hHolomorphicAlgebraicity A B
    (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.nativeMap hHolomorphicAlgebraicity A B g) (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.nativeMap_mdifferentiable hHolomorphicAlgebraicity A B g hg)
  refine ⟨n, hn, a, ha, ?_⟩
  rw [hapull]
  apply LinearMap.ext
  intro c
  apply eB.injective
  have hp := OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicPeriodNaturality.rationalH1Equiv_nativeMap_pullback hHolomorphicAlgebraicity A B g hg f fQ hf hlift hfQ c
  change eB
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom ⟨OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.nativeMap hHolomorphicAlgebraicity A B g,
        (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.nativeMap_mdifferentiable hHolomorphicAlgebraicity A B g hg).continuous⟩) 1 c) = _
  rw [hp]
  erw [hpull (eA c)]
  change (n : ℚ) • eB (u (eA.symm (eA c))) = eB ((n : ℚ) • u c)
  erw [eA.symm_apply_apply, map_smul]

end ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian

namespace ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods
open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.CM
open OAI.Geometry.ComplexTorus.BettiLattice.CM.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TorusModel.Constructions
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps
section

/-!
The algebraic comparison for the native exponential tori of actual
abelian varieties. A complex-linear equivalence preserving the actual
period lattices is algebraized to a group-preserving scheme isomorphism.
The point formula records the exact exponential/uniformization map.
-/

/-- The already proved HolomorphicAlgebraicity theorem, used without an input hypothesis. -/
abbrev algebraization : OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.HolomorphicAlgebraicityInput := OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.CM.holomorphic_group_hom_is_algebraic

abbrev torus (A : OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) := OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TorusModel.Constructions.abelianTorus algebraization A

local instance (A : OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth
local instance (A : OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsProper A.toOver.hom :=
  A.variety.presentation.projective.isProper

/-- Inverse holomorphic homomorphisms of the actual exponential tori
give inverse algebraic group homomorphisms of the original varieties. -/
theorem algebraic_iso_of_inverse_torus_maps (A B : OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (g : (torus A).Point →+ (torus B).Point)
    (h : (torus B).Point →+ (torus A).Point)
    (hg : Geometry.ComplexTorus.BettiLattice.CM.Construction.Holomorphic g) (hh : Geometry.ComplexTorus.BettiLattice.CM.Construction.Holomorphic h)
    (hleft : ∀ x, h (g x) = x) (hright : ∀ y, g (h y) = y) :
    ∃ e : A.toOver ≅ B.toOver, IsMonHom e.hom ∧
      ∀ x, OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom x = OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.nativeMap algebraization B A g x := by
  obtain ⟨f, hf, hfp⟩ := algebraization A B (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.nativeMap algebraization B A g)
    (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.nativeMap_mdifferentiable algebraization B A g hg)
  obtain ⟨b, hb, hbp⟩ := algebraization B A (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.nativeMap algebraization A B h)
    (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.nativeMap_mdifferentiable algebraization A B h hh)
  have hgf (x : OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) :
      OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.nativeMap algebraization A B h (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.nativeMap algebraization B A g x) = x := by
    simp only [OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.nativeMap_apply]
    erw [Homeomorph.symm_apply_apply, hleft, Homeomorph.apply_symm_apply]
  have hfg (x : OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver) :
      OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.nativeMap algebraization B A g (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.nativeMap algebraization A B h x) = x := by
    simp only [OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.nativeMap_apply]
    erw [Homeomorph.symm_apply_apply, hright, Homeomorph.apply_symm_apply]
  have hfb : f ≫ b = 𝟙 A.toOver := by
    apply OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.schemeMap_ext
    intro x
    change x ≫ (f ≫ b) = x ≫ 𝟙 _
    rw [← Category.assoc, Category.comp_id]
    change OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map b (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x) = x
    rw [hbp, hfp]
    exact hgf x
  have hbf : b ≫ f = 𝟙 B.toOver := by
    apply OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.schemeMap_ext
    intro x
    change x ≫ (b ≫ f) = x ≫ 𝟙 _
    rw [← Category.assoc, Category.comp_id]
    change OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map b x) = x
    rw [hfp, hbp]
    exact hfg x
  exact ⟨⟨f, b, hfb, hbf⟩, hf, hfp⟩

/-- A complex-linear equivalence preserving the actual exponential
lattices is induced by an algebraic group isomorphism, with its exact
value on every point of the native uniformization. -/
theorem algebraic_iso_of_lattice_equiv (A B : OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃ₗ[ℂ] OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B)
    (he : ∀ v ∈ OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A, e v ∈ OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B)
    (hei : ∀ w ∈ OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B, e.symm w ∈ OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    ∃ a : A.toOver ≅ B.toOver, IsMonHom a.hom ∧
      ∀ v : OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A,
        OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a.hom
          (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph algebraization A ((torus A).proj v)) =
            OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph algebraization B ((torus B).proj (e v)) := by
  let g : (torus A).Point →+ (torus B).Point :=
    Geometry.ComplexTorus.BettiLattice.CM.Construction.descend (A := torus A) (B := torus B) e.toLinearMap he
  let h : (torus B).Point →+ (torus A).Point :=
    Geometry.ComplexTorus.BettiLattice.CM.Construction.descend (A := torus B) (B := torus A) e.symm.toLinearMap hei
  have hl (x : (torus A).Point) : h (g x) = x := by
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective x
    change OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A at v
    change (torus A).proj (e.symm (e v)) = (torus A).proj v
    rw [e.symm_apply_apply]
  have hr (y : (torus B).Point) : g (h y) = y := by
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective y
    change OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B at v
    change (torus B).proj (e (e.symm v)) = (torus B).proj v
    rw [e.apply_symm_apply]
  obtain ⟨a, ha, hap⟩ := algebraic_iso_of_inverse_torus_maps A B g h
    (Geometry.ComplexTorus.BettiLattice.CM.Construction.descend_holomorphic (A := torus A) (B := torus B) e.toLinearMap he)
    (Geometry.ComplexTorus.BettiLattice.CM.Construction.descend_holomorphic (A := torus B) (B := torus A) e.symm.toLinearMap hei) hl hr
  refine ⟨a, ha, fun v => ?_⟩
  rw [hap, OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.nativeMap_periodHomeomorph]
  rfl

end

/-!
Actual algebraic group maps on the native period tori. The local lifts
are constructed using the quotient charts, before applying the proved
linear-lifting theorem BettiLattice. No lifting or cohomological faithfulness
hypothesis is imposed on the algebraic maps.
-/

open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

/-- Manifold differentiability produces BettiLattice's actual local holomorphic
lifts by composing with a local inverse of the lattice covering. -/
theorem local_lifts_of_mdifferentiable
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ]
    (Γ : Submodule ℤ W) [DiscreteTopology Γ]
    (g : OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Torus.Constructions.LatticeQuotient.Point Λ → OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Torus.Constructions.LatticeQuotient.Point Γ)
    (hg : MDifferentiable (𝓘(ℂ, V)) (𝓘(ℂ, W)) g) :
    ∀ v : V, ∃ (s : Set V) (F : V → W),
      IsOpen s ∧ v ∈ s ∧ DifferentiableOn ℂ F s ∧
      ∀ w ∈ s, g (QuotientAddGroup.mk w) = QuotientAddGroup.mk (F w) := by
  intro v
  let q : V → OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Torus.Constructions.LatticeQuotient.Point Λ := QuotientAddGroup.mk
  let p := g (q v)
  let e := OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Torus.Constructions.LatticeQuotient.chart Γ p
  let s := (g ∘ q) ⁻¹' e.source
  let F : V → W := e ∘ g ∘ q
  have hd : MDifferentiable (𝓘(ℂ, V)) (𝓘(ℂ, W)) (g ∘ q) :=
    hg.comp ((OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Torus.Constructions.LatticeQuotient.projection_contMDiff Λ).mdifferentiable (by simp))
  refine ⟨s, F, e.open_source.preimage hd.continuous,
    OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Torus.Constructions.LatticeQuotient.mem_chart_source Γ p, ?_, ?_⟩
  · intro w hw
    have hchart : g (q w) ∈ (chartAt W p).source := hw
    have h := (mdifferentiableAt_iff_target_of_mem_source (f := g ∘ q) hchart).mp (hd w)
    exact (mdifferentiableAt_iff_differentiableAt.mp h.2).differentiableWithinAt
  · intro w hw
    have h := e.left_inv hw
    rw [OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Torus.Constructions.LatticeQuotient.chart_symm] at h
    exact h.symm

local instance (A : OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth
local instance (A : OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsProper A.toOver.hom :=
  A.variety.presentation.projective.isProper

/-- The group map on the actual exponential quotients induced by an
algebraic group morphism. -/
def algebraicTorusMap {A B : OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (f : A.toOver ⟶ B.toOver) [IsMonHom f] :
    (torus A).Point →+ (torus B).Point where
  toFun x := (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.periodAddEquiv algebraization B).symm
    (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.periodAddEquiv algebraization A x))
  map_zero' := by
    change (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.periodAddEquiv algebraization B).symm
      (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.periodAddEquiv algebraization A 0)) = 0
    rw [(OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.periodAddEquiv algebraization A).map_zero]
    have h : OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f 1 = 1 := MonObj.one_comp f
    erw [h, (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.periodAddEquiv algebraization B).symm.map_zero]
  map_add' x y := by
    rw [(OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.periodAddEquiv algebraization A).map_add]
    have h (u v : OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) :
        OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (u * v) =
          OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f u * OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f v :=
      MonObj.mul_comp u v f
    erw [h, (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.periodAddEquiv algebraization B).symm.map_add]
    rfl

theorem algebraicTorusMap_holomorphic {A B : OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (f : A.toOver ⟶ B.toOver) [IsMonHom f] : Geometry.ComplexTorus.BettiLattice.CM.Construction.Holomorphic (algebraicTorusMap f) := by
  apply local_lifts_of_mdifferentiable (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B)
  exact (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph_symm_mdifferentiable algebraization B).comp
    (((OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complex_contMDiff_map f ∞).mdifferentiable (by simp)).comp
      (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph_mdifferentiable algebraization A))

theorem nativeMap_algebraicTorusMap {A B : OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (f : A.toOver ⟶ B.toOver) [IsMonHom f] (x : OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) :
    OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.nativeMap algebraization B A (algebraicTorusMap f) x = OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x := by
  change (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.periodAddEquiv algebraization B)
    ((OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.periodAddEquiv algebraization B).symm
      (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ((OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.periodAddEquiv algebraization A)
        ((OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.periodAddEquiv algebraization A).symm x)))) = _
  erw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- Every actual algebraic group map has the unique native complex-linear
lift preserving its actual integral period lattice. -/
theorem algebraic_map_linear_lift {A B : OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (f : A.toOver ⟶ B.toOver) [IsMonHom f] :
    ∃! L : OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℂ] OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B,
      Geometry.ComplexTorus.BettiLattice.CM.Construction.PreservesLattice (A := torus A) (B := torus B) L ∧
        Geometry.ComplexTorus.BettiLattice.CM.Construction.Lifts (algebraicTorusMap f) L :=
  Geometry.ComplexTorus.BettiLattice.CM.Construction.holomorphic_linear_lift (torus A) (torus B) (algebraicTorusMap f)
    (algebraicTorusMap_holomorphic f)

end ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods

end

end OAI
