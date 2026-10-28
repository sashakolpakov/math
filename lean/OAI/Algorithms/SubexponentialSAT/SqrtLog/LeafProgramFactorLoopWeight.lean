import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopContract
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentSemantics

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop
open SubexponentialSAT SubexpLiftRing SubexpQuarticRing MomentsProgram MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The physical weight service reads only the three context masks and the
stored zero/one words. Its result is independent of accumulator bytes and registers. -/
theorem weight_eq {p t n d : ℕ} [Fact p.Prime]
    (e : Product.Store) (left seed : Raw n (baseWidth p t) d)
    (high : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (c : AssignmentContext) (x : List Bool)
    (zero one : RingProgram.Code (Word (baseWidth p t)) d)
    (hc : c.Matches high) (hx : high 174=x)
    (hz : high 190=RingProgram.flat zero) (ho : high 207=RingProgram.flat one) :
    LeafAssignmentSetupProgram.weight (machine regs (Product.working e left [] seed) high)=
      RingProgram.flat (AssignmentSemantics.coefficient zero one x c.support c.headMask) := by
  rw [AssignmentSemantics.coefficient_bytes]
  rcases hc with ⟨hs,hh,_,_⟩
  simp [LeafAssignmentSetupProgram.weight,machine,hx,hs,hh,hz,ho]

/-- Boolean weight interpretation for any actual relational accumulator
witness returned by the factor fold. -/
theorem relation_contribution_denote {p t n d : ℕ} [Fact p.Prime]
    {R : Type*} [CommRing R]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R) (u J : ℕ)
    (zero oneCoeff : RingProgram.Code (Word (baseWidth p t)) d)
    (hzero : RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis zero=0)
    (honeCoeff : RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis oneCoeff=1)
    (one : Raw n (baseWidth p t) d)
    (hone : NativeSemantics.rawDenote
      (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis) one=
        Squarefree.canonical u J 1)
    (step : AssignmentContext → List Bool → Raw n (baseWidth p t) d → ℕ → Raw n (baseWidth p t) d → Prop)
    (ids : AssignmentContext → List Bool → List ℕ)
    (factor : AssignmentContext → List Bool → ℕ → Squarefree.Jet (Fin n) R)
    (hstep : ∀ c x a id b, step c x a id b →
      NativeSemantics.rawDenote (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis) b=
        Squarefree.canonical u J
          (NativeSemantics.rawDenote (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis) a * factor c x id))
    (c : AssignmentContext) (x : List Bool) (value : Contribution n (baseWidth p t) d)
    (hr : assignmentRelation step ids one
      (fun c x => AssignmentSemantics.coefficient zero oneCoeff x c.support c.headMask) c x value) :
    contributionDenote p t M cache scalar basis value=
      Moments.ringScalar (if LeafWeightProgram.good x c.support c.headMask then (1:R) else 0) *
        Squarefree.canonical u J ((ids c x).map (factor c x)).prod := by
  rcases hr with ⟨hw,hfold⟩
  have hp := runRel_product u J
    (NativeSemantics.rawDenote (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis))
    (factor c x) (step c x) (hstep c x) hfold hone
  have hc : RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis value.1=
      if LeafWeightProgram.good x c.support c.headMask then (1:R) else 0 := by
    rw [hw]
    cases hg : LeafWeightProgram.good x c.support c.headMask <;>
      simpa [AssignmentSemantics.coefficient,hg] using (by
        first | exact hzero | exact honeCoeff)
  exact contributionDenote_eq p t M cache scalar basis _ _ _ hc hp

end SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop

end OAI.Algorithms
