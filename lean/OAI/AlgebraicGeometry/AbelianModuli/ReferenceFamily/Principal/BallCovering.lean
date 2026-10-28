import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.ArchimedeanDiscrete
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.BallRealization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.BallOrbitQuotient
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProperActionTransport
import OAI.NumberTheory.ArithmeticGroups.TorsionFreeLevel
import OAI.Geometry.ComplexBall.Free
import Mathlib.Topology.Covering.Quotient

/-! # Ball Covering -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.BallCovering.RankThreePELDatum

noncomputable section

/-! The literal principal arithmetic action is properly discontinuous.
At the proved torsion-free levels its original orbit projection is a
surjective topological covering. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible) (N : ℕ)

local instance : LocallyCompactSpace P.Domain := P.domainOpen.isOpen.locallyCompactSpace

include hP in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.principalBallAction_properlyDiscontinuous :
    ProperlyDiscontinuousSMul (Groups.principalSpecialUnitary P.b P.lattice N) P.Domain := by
  let Γ := P.principalArchimedeanSubgroup N
  let : DiscreteTopology Γ := P.principalArchimedean_discrete hP N
  have him : (P.μ P.b).im = 0 := by
    have h := congrArg P.μ hP.2.1
    rw [NumberField.IsCMField.complexEmbedding_complexConj] at h
    exact Complex.conj_eq_iff_im.mp h
  let : ProperlyDiscontinuousSMul Γ (Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball (P.μ P.b)) :=
    Geometry.ComplexBall.ArithmeticQuotientBoostBall.discrete_ballAction_properlyDiscontinuous _ him hP.2.2.2.1 Γ
  let f : Groups.principalSpecialUnitary P.b P.lattice N → Γ := fun g => ⟨P.principalArchimedeanMap N g, ⟨g, rfl⟩⟩
  have hf : Function.Injective f := by
    intro g h he
    exact P.principalArchimedeanMap_injective N (congrArg Subtype.val he)
  exact ProperActionTransport.properlyDiscontinuous_of_equivariant_injection f hf P.arithmeticBallEquiv
    (P.arithmeticBallEquiv_action N)

include hP in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.principalBallAction_free
    (hN : 3 ≤ N) :
    IsCancelSMul (Groups.principalSpecialUnitary P.b P.lattice N) P.Domain := by
  let : ProperlyDiscontinuousSMul (Groups.principalSpecialUnitary P.b P.lattice N) P.Domain :=
    P.principalBallAction_properlyDiscontinuous hP N
  apply Geometry.ComplexBall.Free.ArithmeticQuotient.free_of_properlyDiscontinuous_torsionFree
  intro g k hk he
  have hL : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice P.lattice := hP.2.2.2.2.2.2.2.2.2.1
  exact Subtype.ext (NumberTheory.ArithmeticGroups.Levels.CongruenceLevel.principalLevel_torsion_free P.b P.lattice hL N hN g.val
    ((Groups.mem_principalSpecialUnitary P.b P.lattice N g.val).mp g.property).1 k hk (congrArg Subtype.val he))

include hP in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.principalOrbitProjection_covering
    (hN : 3 ≤ N) :
    IsCoveringMap (P.principalOrbitProjection N) := by
  let : ProperlyDiscontinuousSMul (Groups.principalSpecialUnitary P.b P.lattice N) P.Domain :=
    P.principalBallAction_properlyDiscontinuous hP N
  let : IsCancelSMul (Groups.principalSpecialUnitary P.b P.lattice N) P.Domain := P.principalBallAction_free hP N hN
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.principalOrbitProjection_surjective : Function.Surjective (P.principalOrbitProjection N) :=
  Quotient.mk_surjective

include hP in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.principalOrbitQuotient_hausdorff : T2Space (Quotient (P.principalOrbitSetoid N)) := by
  let : ProperlyDiscontinuousSMul (Groups.principalSpecialUnitary P.b P.lattice N) P.Domain :=
    P.principalBallAction_properlyDiscontinuous hP N
  exact inferInstanceAs (T2Space (MulAction.orbitRel.Quotient (Groups.principalSpecialUnitary P.b P.lattice N) P.Domain))

include hP in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.principalOrbitQuotient_connected : ConnectedSpace (Quotient (P.principalOrbitSetoid N)) := by
  let : ConnectedSpace P.Domain := P.domain_connected hP
  exact (P.principalOrbitProjection_surjective N).connectedSpace continuous_quotient_mk'

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.BallCovering.RankThreePELDatum
