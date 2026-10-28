import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionFinalAssembly

namespace OAI.Algorithms

/-! Conditional final wrappers.  No theorem in this module supplies the native
mass/count service contract: that remaining implementation obligation is an
explicit field of `NativeServices`. -/
namespace SubexponentialSAT.SqrtLog.Execution.Final
open SubexponentialSAT BitProgram StructuredCalls SubexpMainProgram
open Statement

theorem feasible_pair_of_history
    (c : SubexponentialSAT.SubexpSetupProgram.Config)
    (hc : 896 < SubexponentialSAT.SubexpSetupProgram.helperSize c)
    (mass acceptedCount : Cmd 40 896) (Ct At : ℝ) (dt : ℕ)
    (hCt : 1 ≤ Ct) (hAt : 0 ≤ At) (hdt : 0 < dt)
    (hsupply : ObservedHistoryContract c mass acceptedCount Ct At dt) :
    Feasible c.k ∧ BinaryIdentifierFeasible c.k := by
  obtain ⟨C,A,d,hC,hA,hd,hcert⟩ :=
    certificates_of_history c hc mass acceptedCount Ct At dt hCt hAt hdt hsupply
  exact feasible_pair_of_eventual_certificates
    (phases c (by decide) (finalLeafPhases c hc mass acceptedCount))
    (singleLeaf (LeafMain.procedure c hc (LeafOuterProgram.command mass acceptedCount)))
    c.k C A d hC hA hd hcert

/-- Every field is chosen before the input size or formula.  In particular,
`measured` must be proved for the actual fixed native instruction tables. -/
structure NativeServices (width : ℕ) where
  config : SubexponentialSAT.SubexpSetupProgram.Config
  width_eq : config.k=width
  fits : 896 < SubexponentialSAT.SubexpSetupProgram.helperSize config
  mass : Cmd 40 896
  acceptedCount : Cmd 40 896
  tailConstant : ℝ
  tailExponent : ℝ
  degree : ℕ
  constant_ge : 1 ≤ tailConstant
  exponent_nonneg : 0 ≤ tailExponent
  degree_pos : 0 < degree
  measured : ObservedHistoryContract config mass acceptedCount tailConstant tailExponent degree

theorem NativeServices.feasible_pair {width : ℕ} (s : NativeServices width) :
    Feasible width ∧ BinaryIdentifierFeasible width := by
  simpa only [s.width_eq] using feasible_pair_of_history s.config s.fits s.mass
    s.acceptedCount s.tailConstant s.tailExponent s.degree s.constant_ge s.exponent_nonneg
    s.degree_pos s.measured

/-- The existing real finite-cutoff and binary-identifier programs finish both
pinned targets once, and only once, the native service family is supplied. -/
theorem fullMainTheorem_of_services
    (supplied : ∀ width : ℕ, 3 ≤ width → Nonempty (NativeServices width)) :
    FullMainTheorem := by
  constructor
  · intro width hw
    obtain ⟨s⟩ := supplied width hw
    exact s.feasible_pair.1
  · intro width hw
    obtain ⟨s⟩ := supplied width hw
    exact s.feasible_pair.2

theorem mainTheorem_of_services
    (supplied : ∀ width : ℕ, 3 ≤ width → Nonempty (NativeServices width)) :
    MainTheorem := (fullMainTheorem_of_services supplied).1

theorem binaryIdentifierMainTheorem_of_services
    (supplied : ∀ width : ℕ, 3 ≤ width → Nonempty (NativeServices width)) :
    BinaryIdentifierMainTheorem := (fullMainTheorem_of_services supplied).2

end SubexponentialSAT.SqrtLog.Execution.Final

end OAI.Algorithms
