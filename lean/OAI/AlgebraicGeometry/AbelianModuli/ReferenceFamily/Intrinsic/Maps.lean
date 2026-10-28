import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion
import OAI.Geometry.ComplexTorus.BettiLattice
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveMaps

/-! # Maps -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps

/-! Actual algebraic maps on the native exponential quotients. This
uses the proved BettiLattice and HolomorphicAlgebraicity results and the native covering charts;
no Hodge-cohomology comparison is needed for this construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.Geometry.ComplexTorus.BettiLattice.CM.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

abbrev algebraization : HodgeConjecture.DegreeTwo.Transport.Constructions.HolomorphicAlgebraicityInput := Torsion.IntrinsicTorsion.e06Input

def torus (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Geometry.ComplexTorus.BettiLattice.CM.Construction.Torus where
  V := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A
  lattice := HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A
  full := HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice_full algebraization A

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsProper A.toOver.hom :=
  A.variety.presentation.projective.isProper

def periodAddEquiv (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    (torus A).Point ≃+ Additive (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) where
  toEquiv := (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph algebraization A).toEquiv
  map_add' x y := by
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective y
    exact HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap_add (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) v w

theorem local_lifts_of_mdifferentiable
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ]
    (Γ : Submodule ℤ W) [DiscreteTopology Γ]
    (f : HodgeConjecture.DegreeTwo.Torus.Constructions.LatticeQuotient.Point Λ → HodgeConjecture.DegreeTwo.Torus.Constructions.LatticeQuotient.Point Γ)
    (hf : MDifferentiable (𝓘(ℂ, V)) (𝓘(ℂ, W)) f) :
    ∀ v : V, ∃ (s : Set V) (F : V → W),
      IsOpen s ∧ v ∈ s ∧ DifferentiableOn ℂ F s ∧
      ∀ w ∈ s, f (QuotientAddGroup.mk w) = QuotientAddGroup.mk (F w) := by
  intro v
  let q : V → HodgeConjecture.DegreeTwo.Torus.Constructions.LatticeQuotient.Point Λ := QuotientAddGroup.mk
  let p := f (q v)
  let e := HodgeConjecture.DegreeTwo.Torus.Constructions.LatticeQuotient.chart Γ p
  let s := (f ∘ q) ⁻¹' e.source
  let F : V → W := e ∘ f ∘ q
  have hd : MDifferentiable (𝓘(ℂ, V)) (𝓘(ℂ, W)) (f ∘ q) :=
    hf.comp ((HodgeConjecture.DegreeTwo.Torus.Constructions.LatticeQuotient.projection_contMDiff Λ).mdifferentiable (by simp))
  refine ⟨s, F, e.open_source.preimage hd.continuous,
    HodgeConjecture.DegreeTwo.Torus.Constructions.LatticeQuotient.mem_chart_source Γ p, ?_, ?_⟩
  · intro w hw
    have hchart : f (q w) ∈ (chartAt W p).source := hw
    have h := (mdifferentiableAt_iff_target_of_mem_source (f := f ∘ q) hchart).mp (hd w)
    exact (mdifferentiableAt_iff_differentiableAt.mp h.2).differentiableWithinAt
  · intro w hw
    have h := e.left_inv hw
    rw [HodgeConjecture.DegreeTwo.Torus.Constructions.LatticeQuotient.chart_symm] at h
    exact h.symm

def algebraicTorusMap {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (f : A.toOver ⟶ B.toOver) [IsMonHom f] :
    (torus A).Point →+ (torus B).Point where
  toFun x := (periodAddEquiv B).symm
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (periodAddEquiv A x))
  map_zero' := by
    change (periodAddEquiv B).symm
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (periodAddEquiv A 0)) = 0
    rw [(periodAddEquiv A).map_zero]
    have h : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f 1 = 1 := MonObj.one_comp f
    erw [h, (periodAddEquiv B).symm.map_zero]
  map_add' x y := by
    rw [(periodAddEquiv A).map_add]
    have h (u v : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) :
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (u * v) =
          ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f u * ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f v := MonObj.mul_comp u v f
    erw [h, (periodAddEquiv B).symm.map_add]
    rfl

theorem algebraicTorusMap_holomorphic {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (f : A.toOver ⟶ B.toOver) [IsMonHom f] : Geometry.ComplexTorus.BettiLattice.CM.Construction.Holomorphic (algebraicTorusMap f) := by
  apply local_lifts_of_mdifferentiable (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B)
  exact (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph_symm_mdifferentiable algebraization B).comp
    (((Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complex_contMDiff_map f ∞).mdifferentiable (by simp)).comp
      (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph_mdifferentiable algebraization A))

theorem algebraic_map_linear_lift {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (f : A.toOver ⟶ B.toOver) [IsMonHom f] :
    ∃! L : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B,
      Geometry.ComplexTorus.BettiLattice.CM.Construction.PreservesLattice (A := torus A) (B := torus B) L ∧ Geometry.ComplexTorus.BettiLattice.CM.Construction.Lifts (algebraicTorusMap f) L :=
  Geometry.ComplexTorus.BettiLattice.CM.Construction.holomorphic_linear_lift (torus A) (torus B) (algebraicTorusMap f) (algebraicTorusMap_holomorphic f)

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps
open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open OAI.Geometry.ComplexTorus.BettiLattice.CM.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj
open scoped _root_.CategoryTheory.Obj
section

/-! Algebraic group maps act functorially on the actual native period
spaces. Their complex-linear lifts preserve the actual period lattices,
and addition and composition agree with those of the algebraic maps. -/

variable {A B C : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}

instance nativeOne_isMonHom (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    IsMonHom (1 : A.toOver ⟶ B.toOver) :=
  inferInstanceAs (IsMonHom (toUnit A.toOver ≫ η[B.toOver]))

instance nativeMul_isMonHom (f h : A.toOver ⟶ B.toOver) [IsMonHom f] [IsMonHom h] :
    IsMonHom (f * h) := inferInstanceAs (IsMonHom (lift f h ≫ μ[B.toOver]))

def linearLift (f : A.toOver ⟶ B.toOver) [IsMonHom f] :
    HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B := (IntrinsicAlgebraicMaps.algebraic_map_linear_lift f).choose

theorem linearLift_congr (f h : A.toOver ⟶ B.toOver) [IsMonHom f] [IsMonHom h]
    (e : f = h) : linearLift f = linearLift h := by
  cases e
  rfl

theorem linearLift_preserves (f : A.toOver ⟶ B.toOver) [IsMonHom f] :
    Geometry.ComplexTorus.BettiLattice.CM.Construction.PreservesLattice (A := IntrinsicAlgebraicMaps.torus A) (B := IntrinsicAlgebraicMaps.torus B) (linearLift f) :=
  (IntrinsicAlgebraicMaps.algebraic_map_linear_lift f).choose_spec.1.1

theorem linearLift_lifts (f : A.toOver ⟶ B.toOver) [IsMonHom f] :
    Geometry.ComplexTorus.BettiLattice.CM.Construction.Lifts (IntrinsicAlgebraicMaps.algebraicTorusMap f) (linearLift f) :=
  (IntrinsicAlgebraicMaps.algebraic_map_linear_lift f).choose_spec.1.2

theorem linearLift_unique (f : A.toOver ⟶ B.toOver) [IsMonHom f]
    (L : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B)
    (hL : Geometry.ComplexTorus.BettiLattice.CM.Construction.PreservesLattice (A := IntrinsicAlgebraicMaps.torus A) (B := IntrinsicAlgebraicMaps.torus B) L)
    (hl : Geometry.ComplexTorus.BettiLattice.CM.Construction.Lifts (IntrinsicAlgebraicMaps.algebraicTorusMap f) L) : L = linearLift f :=
  (IntrinsicAlgebraicMaps.algebraic_map_linear_lift f).choose_spec.2 L ⟨hL, hl⟩

theorem torusMap_comp (f : A.toOver ⟶ B.toOver) (h : B.toOver ⟶ C.toOver)
    [IsMonHom f] [IsMonHom h] :
    IntrinsicAlgebraicMaps.algebraicTorusMap (f ≫ h) = (IntrinsicAlgebraicMaps.algebraicTorusMap h).comp (IntrinsicAlgebraicMaps.algebraicTorusMap f) := by
  apply AddMonoidHom.ext
  intro x
  let x₀ : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver := (IntrinsicAlgebraicMaps.periodAddEquiv A x).toMul
  have he := (IntrinsicAlgebraicMaps.periodAddEquiv B).apply_symm_apply (Additive.ofMul (x₀ ≫ f))
  exact (congrArg (fun z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints C.toOver =>
      (IntrinsicAlgebraicMaps.periodAddEquiv C).symm (Additive.ofMul z)) (Category.assoc x₀ f h).symm).trans
    (congrArg (fun z : Additive (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver) =>
      (IntrinsicAlgebraicMaps.periodAddEquiv C).symm (Additive.ofMul (z.toMul ≫ h))) he).symm

theorem torusMap_id (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    IntrinsicAlgebraicMaps.algebraicTorusMap (𝟙 A.toOver) = AddMonoidHom.id (IntrinsicAlgebraicMaps.torus A).Point := by
  apply AddMonoidHom.ext
  intro x
  exact (congrArg (fun z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver =>
    (IntrinsicAlgebraicMaps.periodAddEquiv A).symm (Additive.ofMul z))
    (Category.comp_id (IntrinsicAlgebraicMaps.periodAddEquiv A x).toMul)).trans
      ((IntrinsicAlgebraicMaps.periodAddEquiv A).symm_apply_apply x)

theorem torusMap_zero (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    IntrinsicAlgebraicMaps.algebraicTorusMap (1 : A.toOver ⟶ B.toOver) = 0 := by
  apply AddMonoidHom.ext
  intro x
  exact (congrArg (fun z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver =>
    (IntrinsicAlgebraicMaps.periodAddEquiv B).symm (Additive.ofMul z))
    (MonObj.comp_one (IntrinsicAlgebraicMaps.periodAddEquiv A x).toMul)).trans
      (IntrinsicAlgebraicMaps.periodAddEquiv B).symm.map_zero

theorem torusMap_add (f h : A.toOver ⟶ B.toOver) [IsMonHom f] [IsMonHom h] :
    IntrinsicAlgebraicMaps.algebraicTorusMap (f * h) = IntrinsicAlgebraicMaps.algebraicTorusMap f + IntrinsicAlgebraicMaps.algebraicTorusMap h := by
  apply AddMonoidHom.ext
  intro x
  exact (congrArg (fun z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver =>
    (IntrinsicAlgebraicMaps.periodAddEquiv B).symm (Additive.ofMul z))
    (MonObj.comp_mul (IntrinsicAlgebraicMaps.periodAddEquiv A x).toMul f h)).trans
      ((IntrinsicAlgebraicMaps.periodAddEquiv B).symm.map_add _ _)

theorem linearLift_id (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : linearLift (𝟙 A.toOver) = LinearMap.id := by
  symm
  apply linearLift_unique
  · exact fun _ hv => hv
  · intro v
    rw [torusMap_id]
    rfl

theorem linearLift_zero (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    linearLift (1 : A.toOver ⟶ B.toOver) = 0 := by
  symm
  apply linearLift_unique
  · exact fun _ _ => (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B).zero_mem
  · intro v
    rw [torusMap_zero]
    rfl

theorem linearLift_comp (f : A.toOver ⟶ B.toOver) (h : B.toOver ⟶ C.toOver)
    [IsMonHom f] [IsMonHom h] :
    linearLift (f ≫ h) = (linearLift h).comp (linearLift f) := by
  symm
  apply linearLift_unique
  · exact fun v hv => linearLift_preserves h _ (linearLift_preserves f v hv)
  · intro v
    rw [torusMap_comp]
    exact (congrArg (IntrinsicAlgebraicMaps.algebraicTorusMap h) (linearLift_lifts f v)).trans
      (linearLift_lifts h (linearLift f v))

theorem linearLift_add (f h : A.toOver ⟶ B.toOver) [IsMonHom f] [IsMonHom h] :
    linearLift (f * h) = linearLift f + linearLift h := by
  symm
  apply linearLift_unique
  · exact fun v hv => (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B).add_mem
      (linearLift_preserves f v hv) (linearLift_preserves h v hv)
  · intro v
    rw [torusMap_add]
    exact (congrArg₂ (· + ·) (linearLift_lifts f v) (linearLift_lifts h v)).trans
      ((IntrinsicAlgebraicMaps.torus B).proj_add _ _).symm

end

/-! The constructed complex-linear lift agrees with the actual native
uniformization and faithfully determines the algebraic group morphism. -/

variable {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsProper A.toOver.hom :=
  A.variety.presentation.projective.isProper

/-- The native exponential comparison intertwines the algebraic map
with the constructed lift on every complex period vector. -/
theorem linearLift_period (f : A.toOver ⟶ B.toOver) [IsMonHom f] (v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicAlgebraicMaps.algebraization A ((IntrinsicAlgebraicMaps.torus A).proj v)) =
      HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicAlgebraicMaps.algebraization B ((IntrinsicAlgebraicMaps.torus B).proj (linearLift f v)) := by
  have h := congrArg (IntrinsicAlgebraicMaps.periodAddEquiv B) (linearLift_lifts f v)
  exact congrArg Additive.toMul (((IntrinsicAlgebraicMaps.periodAddEquiv B).apply_symm_apply _).symm.trans h)

/-- Equality of the native lifts forces equality of the original
algebraic group morphisms. -/
theorem linearLift_faithful (f h : A.toOver ⟶ B.toOver) [IsMonHom f] [IsMonHom h]
    (he : linearLift f = linearLift h) : f = h := by
  apply ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.schemeMap_ext
  intro x
  obtain ⟨v, hv⟩ := QuotientAddGroup.mk_surjective ((IntrinsicAlgebraicMaps.periodAddEquiv A).symm (Additive.ofMul x))
  have hx : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicAlgebraicMaps.algebraization A ((IntrinsicAlgebraicMaps.torus A).proj v) = x :=
    congrArg Additive.toMul ((congrArg (IntrinsicAlgebraicMaps.periodAddEquiv A) hv).trans
      ((IntrinsicAlgebraicMaps.periodAddEquiv A).apply_symm_apply (Additive.ofMul x)))
  exact (congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) hx.symm).trans
    ((linearLift_period f v).trans
      ((congrArg (fun L : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B =>
        HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicAlgebraicMaps.algebraization B ((IntrinsicAlgebraicMaps.torus B).proj (L v))) he).trans
        ((linearLift_period h v).symm.trans (congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map h) hx))))

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps

end

end OAI
