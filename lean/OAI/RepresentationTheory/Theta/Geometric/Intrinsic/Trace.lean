import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.Action
import OAI.RepresentationTheory.Theta.Geometric.BranchTrace
import OAI.RepresentationTheory.Theta.Geometric.PELTrace

/-! # Trace -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The canonical branch trace specialized to the actual rational SU,
its q-adic matrix embedding, and PoissonAutomorphy's finite Weil action. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [IsTopologicalGroup Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def Data.ActiveHeckeThetaData.integralOpen : OpenSubgroup (SphericalGU.Spherical.SL3 q) where
  toSubgroup := SphericalGU.Spherical.integralSL3 q
  isOpen' := by
    change IsOpen (SphericalGU.Spherical.integralSL3 q : Set (SphericalGU.Spherical.SL3 q))
    rw [← D.localLevel.property]
    exact D.localLevel.val.isOpen

def Data.ActiveHeckeThetaData.nativeBranchTrace (hArithmetic : DenseRange D.rationalFinite) (T : SphericalGU.Spherical.SL3Hecke q) :
    (D.domain → LinearTheta.Cotangent) →ₗ[ℂ] (D.domain → LinearTheta.Cotangent) :=
  letI := D.periodAction
  BranchTrace.activeBranchTrace D.rationalFinite hArithmetic D.integralOpen D.awayLevel D.domain
    (fun g x hx => D.periodMap_preserves g x hx) T

/-- No map identification is an input: both sides use the same constructed
theta series, its derivative and projection. Only rational automorphy and
the explicit Arithmetic density prerequisite enter this finite-trace argument. -/
theorem Data.ActiveHeckeThetaData.native_branch_theta_covariance
    (hArithmetic : DenseRange D.rationalFinite) (hautomorphy : D.HasRationalThetaCovariance)
    (T : SphericalGU.Spherical.SL3Hecke q) (φ : D.sphericalInputs) :
    D.nativeBranchTrace hArithmetic T (Descent.restrictForm D.domain (D.thetaUniversal φ.val)) =
      Descent.restrictForm D.domain (D.thetaUniversal (D.sphericalWeil T φ).val) := by
  let : MulAction D.RationalSU LinearTheta.BallCoordinates := D.periodAction
  apply BranchTrace.canonical_active_branch_trace D.rationalFinite hArithmetic D.integralOpen D.awayLevel
    D.domain (fun g x hx => D.periodMap_preserves g x hx) D.period D.project D.finiteWeil
  intro g f
  funext x
  exact hautomorphy g f x

end

end OAI.RepresentationTheory.Theta.Geometric
