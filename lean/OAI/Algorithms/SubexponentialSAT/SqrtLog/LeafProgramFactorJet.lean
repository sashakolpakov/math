import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorPayload
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyStaging

namespace OAI.Algorithms

/-! The incidence meaning depends only on the merged assignment and the
fixed-high context. Parser and accumulator contents do not enter it. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open PerturbationAssembly DensePolynomialProgram

/-- Project the three physical assignment masters into the incidence ABI. -/
def choiceStore (s : Fin 768 → List Bool) : OuterStore :=
  fun i => if i=546 then s 145 else if i=574 then s 702 else if i=575 then s 703 else []

noncomputable def factorJet {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (n f j : ℕ) (theta : Coeff (baseWidth 3 p.t) d) (s : Fin 768 → List Bool) :=
  sourceIncidenceJet p ps P n f j theta (choiceStore s)

theorem factorJet_staged {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (J n f j : ℕ) (theta : Coeff (baseWidth 3 p.t) d) (a : OuterData)
    (h : CallerInput p.t p.model p.modulus p.cache J p.R theta a n) :
    sourceIncidenceJet p ps P n f j theta (Incidence.staged a).stacks =
      factorJet p ps P n f j theta a.stacks := by
  have hc := Incidence.staged_copy a h.destinations_empty
  unfold sourceIncidenceJet factorJet
  rw [hc (702,574) (by decide),hc (703,575) (by decide),hc (145,546) (by decide)]
  simp [sourceIncidenceJet,choiceStore]

theorem factorJet_frame {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (n f j : ℕ) (theta : Coeff (baseWidth 3 p.t) d) (a b : Fin 768 → List Bool)
    (h145 : a 145=b 145) (h702 : a 702=b 702) (h703 : a 703=b 703) :
    factorJet p ps P n f j theta a=factorJet p ps P n f j theta b := by
  unfold factorJet sourceIncidenceJet
  simp only [choiceStore,show (574:Fin 768)≠546 by decide,show (575:Fin 768)≠546 by decide,
    show (575:Fin 768)≠574 by decide,ite_false,ite_true]
  rw [h145,h702,h703]

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
