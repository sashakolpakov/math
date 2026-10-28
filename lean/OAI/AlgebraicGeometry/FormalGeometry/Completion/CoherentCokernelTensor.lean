import OAI.AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertAdditivity
import OAI.AlgebraicGeometry.FormalGeometry.Completion.CoherentLineBundleTensor

/-! # Coherent Cokernel Tensor -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.CoherentCokernelTensor

noncomputable section

/-! Tensoring an actual coherent cokernel by a line bundle gives the
corresponding difference of actual Hilbert polynomials. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u

def coherentModuleCokernel {X : Scheme.{u}} {M N : X.Modules} (a : M ⟶ N) : X.Modules := cokernel a

instance coherentModuleCokernel_quasicoherent {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (a : M ⟶ N) :
    (coherentModuleCokernel a).IsQuasicoherent := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_cokernel a

instance coherentModuleCokernel_finiteType {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] [N.IsFiniteType] (a : M ⟶ N) :
    (coherentModuleCokernel a).IsFiniteType := SheafCohomology.Projective.CoherentQuotientFiniteType.Scheme.Modules.isFiniteType_cokernel a

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] {r : ℕ} {X : Scheme.{u}}
  (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)) [IsClosedImmersion f]

theorem coherentCokernelTensor_hilbertPolynomial
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] [M.IsFiniteType] [N.IsFiniteType]
    (a : M ⟶ N) [Mono a] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (j : Fin (r + 1)) :
    ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f (CoherentLineBundleTensor.Construction.coherentLineBundleTensor (coherentModuleCokernel a) L) j =
      ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f (CoherentLineBundleTensor.Construction.coherentLineBundleTensor N L) j -
        ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f (CoherentLineBundleTensor.Construction.coherentLineBundleTensor M L) j := by
  let E := SheafCohomology.Projective.InvertibleTensorEquivalence.invertibleRightTensorEquivalence L.sheaf (Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L)
  let T := ShortComplex.mk a (cokernel.π a) (cokernel.condition a)
  have hT : T.ShortExact := { exact := ShortComplex.cokernelSequence_exact a }
  let S := T.map E.functor
  have : S.X₁.IsQuasicoherent := CoherentLineBundleTensor.Construction.coherentLineBundleTensor_quasicoherent M L
  have : S.X₂.IsQuasicoherent := CoherentLineBundleTensor.Construction.coherentLineBundleTensor_quasicoherent N L
  have : S.X₃.IsQuasicoherent := CoherentLineBundleTensor.Construction.coherentLineBundleTensor_quasicoherent (coherentModuleCokernel a) L
  have : S.X₁.IsFiniteType := CoherentLineBundleTensor.Construction.coherentLineBundleTensor_finiteType M L
  have : S.X₂.IsFiniteType := CoherentLineBundleTensor.Construction.coherentLineBundleTensor_finiteType N L
  have : S.X₃.IsFiniteType := CoherentLineBundleTensor.Construction.coherentLineBundleTensor_finiteType (coherentModuleCokernel a) L
  have he := ClosedHilbertAdditivity.Construction.closedProjectiveHilbertPolynomial_add_of_shortExact f S (hT.map_of_exact E.functor) j
  change ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f (CoherentLineBundleTensor.Construction.coherentLineBundleTensor N L) j =
    ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f (CoherentLineBundleTensor.Construction.coherentLineBundleTensor M L) j +
      ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f (CoherentLineBundleTensor.Construction.coherentLineBundleTensor (coherentModuleCokernel a) L) j at he
  rw [he, add_sub_cancel_left]

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.CoherentCokernelTensor
