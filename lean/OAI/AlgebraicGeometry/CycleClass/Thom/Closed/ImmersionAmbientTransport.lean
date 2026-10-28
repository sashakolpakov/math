import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.HolomorphicHomeomorph
import OAI.AlgebraicGeometry.CycleClass.Thom.AmbientNaturality

/-! # Immersion Ambient Transport -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionAmbientTransport.Constructions

noncomputable section

/-! Transporting an actual closed complex immersion by a holomorphic ambient homeomorphism preserves its canonical Thom class. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.HolomorphicHomeomorph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.AmbientNaturality.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TransportRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.AmbientTransport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V V' : ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (e : V.analyticSpace ≃ₜ V'.analyticSpace)
  (he : ContMDiff 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, V'.analyticModel) ω e)
  (hei : ContMDiff 𝓘(ℂ, V'.analyticModel) 𝓘(ℂ, V.analyticModel) ω e.symm)
  (hd : V.complexDimension = V'.complexDimension)

include he hei in
theorem transported_differential_injective (x : Z.regularAnalyticSpace) :
    Function.Injective (mfderiv 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, V'.analyticModel)
      (e ∘ Z.regularComplementInclusion) x) := by
  rw [mfderiv_comp x (he.mdifferentiable (by simp) _) (Z.holomorphic.mdifferentiable (by simp) x)]
  exact (HolomorphicHomeomorph.Constructions.homeomorph_mfderiv_bijective e (he.mdifferentiable (by simp))
    (hei.mdifferentiable (by simp)) _).injective.comp (Z.differential_injective x)

def transport : ComplexImmersion.Constructions.ClosedComplexImmersion V' p where
  regularComplexDimension := Z.regularComplexDimension
  regularAnalyticSpace := Z.regularAnalyticSpace
  chartedSpace := inferInstance
  manifold := inferInstance
  regularComplementTopCatMap := TopCat.ofHom
    ⟨e ∘ Z.regularComplementInclusion, e.continuous.comp Z.continuous_regularComplementInclusion⟩
  holomorphic := he.comp Z.holomorphic
  differential_injective := transported_differential_injective Z e he hei
  closed := e.isClosedEmbedding.comp Z.closed
  regularComplexDimension_add_codimension := Z.regularComplexDimension_add_codimension.trans hd

theorem transport_Thom :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPair.TransportRestriction.Constructions.ambientTransportMap e)
      (NormalPair.TransportRestriction.Constructions.ambientTransportMapsTo Z.regularComplementInclusion e) (2 * p)
      (transport Z e he hei hd).regularThomClass = Z.regularThomClass :=
  AmbientNaturality.Constructions.complexThomClassInDegree_ambientTransport Z.regularComplementInclusion Z.holomorphic
    Z.differential_injective Z.closed e (he.mdifferentiable (by simp)) (hei.mdifferentiable (by simp))
    (he.comp Z.holomorphic) (transported_differential_injective Z e he hei)
    (e.isClosedEmbedding.comp Z.closed) p Z.regularComplement_complexImmersionCodimension
    (transport Z e he hei hd).regularComplement_complexImmersionCodimension

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionAmbientTransport.Constructions
