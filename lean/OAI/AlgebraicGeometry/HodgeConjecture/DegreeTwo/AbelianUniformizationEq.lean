import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicProductMaps
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialComplex
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ComponentsRange
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FiniteImagesEq
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveVarietyCompactness

/-! # Abelian Uniformization Eq -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

noncomputable section

/-!
# DegreeTwo: uniformization of the actual abelian variety

HolomorphicAlgebraicity rules out extra analytic components: an open exponential image splits off
a locally constant group endomorphism, which HolomorphicAlgebraicity makes algebraic. Its finite
image must be constant by irreducibility. Hence the actual exponential is
surjective, and its actual periods form a full discrete lattice.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff _root_.Topology _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicProductMaps.Constructions.IntrinsicAbelianLieGroup OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialComplex.Constructions.Exponential

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : CompactSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) :=
  A.variety.presentation.complexPoints_compactSpace
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) :=
  A.variety.presentation.complexPoints_t2Space

/-- HolomorphicAlgebraicity and irreducibility force every locally constant group endomorphism
of the native analytic point group to be trivial. -/
theorem locallyConstant_groupHom_eq_one (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver →* ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (hf : IsLocallyConstant f) : ∀ x, f x = 1 := by
  have hd : MDifferentiable (𝓘(ℂ, Transport.Constructions.AbelianModel A)) (𝓘(ℂ, Transport.Constructions.AbelianModel A)) f := by
    intro x
    have heq : (f : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
        =ᶠ[𝓝 x] (fun _ => f x) := hf.eventually_eq x
    exact heq.mdifferentiableAt_iff.mpr mdifferentiableAt_const
  obtain ⟨g, hg, hgf⟩ := hHolomorphicAlgebraicity A A f hd
  have heq : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g = f := funext hgf
  have hfin : (Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g)).Finite := by
    rw [heq]
    exact hf.range_finite
  intro x
  have h := FiniteImagesEq.Constructions.FiniteImages.map_eq_of_finite_range g hfin x (1 : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
  rw [hgf, hgf, f.map_one] at h
  exact h

/-- The actual analytic space of the abelian variety is connected. This is
derived from HolomorphicAlgebraicity, the constructed exponential, and algebraic irreducibility. -/
theorem native_connectedSpace (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    ConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) := by
  let C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver
  let E := Transport.Constructions.AbelianModel A
  let : IsTopologicalGroup C := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ∞
  let p := ExponentialLocal.Constructions.Exponential.expAddHom (E := E) (C := C)
  have hopen : IsOpen (p.range : Set (Additive C)) := by
    change IsOpen (Set.range (ExponentialM.Constructions.Exponential.expMap (E := E) (C := C)))
    simpa only [Set.image_univ] using
      (ExponentialLocal.Constructions.Exponential.expMap_isLocalHomeomorph (E := E) (C := C)).isOpenMap Set.univ isOpen_univ
  obtain ⟨h, hl, hk⟩ := ComponentsRange.Constructions.Components.exists_locallyConstant_projection p hopen
  let f : C →* C :=
    { toFun := fun x => Additive.toMul (h (Additive.ofMul x))
      map_one' := h.map_zero
      map_mul' := h.map_add }
  have hf : ∀ x, f x = 1 := locallyConstant_groupHom_eq_one hHolomorphicAlgebraicity A f hl
  have hs : Function.Surjective p := by
    intro x
    apply (hk x).mp
    exact hf x
  exact hs.connectedSpace (ExponentialM.Constructions.Exponential.expMap_continuous (E := E) (C := C))

/-- The period lattice is the kernel of the actual native exponential. -/
def periodLattice (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Submodule ℤ (Transport.Constructions.AbelianModel A) :=
  ExponentialLocal.Constructions.Exponential.expLattice (E := Transport.Constructions.AbelianModel A) (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)

instance periodLattice_discrete (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : DiscreteTopology (periodLattice A) :=
  ExponentialLocal.Constructions.Exponential.expLattice_discrete

/-- Compactness and the proved connectedness make the actual periods full. -/
theorem periodLattice_full (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    IsZLattice ℝ (periodLattice A) := by
  let : ConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) := native_connectedSpace hHolomorphicAlgebraicity A
  exact ExponentialLocal.Constructions.Exponential.expLattice_full

/-- The constructed quotient comparison uses the native abelian-variety
point space and its existing topology. -/
def periodHomeomorph (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    (Transport.Constructions.AbelianModel A ⧸ (periodLattice A).toAddSubgroup) ≃ₜ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver := by
  let : ConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) := native_connectedSpace hHolomorphicAlgebraicity A
  exact ExponentialLocal.Constructions.Exponential.expQuotientHomeomorph (E := Transport.Constructions.AbelianModel A) (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)

theorem periodHomeomorph_mdifferentiable (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    MDifferentiable (𝓘(ℂ, Transport.Constructions.AbelianModel A)) (𝓘(ℂ, Transport.Constructions.AbelianModel A))
      (periodHomeomorph hHolomorphicAlgebraicity A) := by
  let : ConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) := native_connectedSpace hHolomorphicAlgebraicity A
  exact ExponentialComplex.Constructions.Exponential.expQuotientHomeomorph_mdifferentiable

theorem periodHomeomorph_symm_mdifferentiable (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    MDifferentiable (𝓘(ℂ, Transport.Constructions.AbelianModel A)) (𝓘(ℂ, Transport.Constructions.AbelianModel A))
      (periodHomeomorph hHolomorphicAlgebraicity A).symm := by
  let : ConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) := native_connectedSpace hHolomorphicAlgebraicity A
  exact ExponentialComplex.Constructions.Exponential.expQuotientHomeomorph_symm_mdifferentiable

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
