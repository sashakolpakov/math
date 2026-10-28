import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTAtZero
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialPowerProgram

namespace OAI.Algorithms

/-!
# Selected-layout inputs for the concrete CRT controller

This bridge keeps the actual node and fixed-polynomial jet readback premises
explicit.  Any scalar inverses satisfying the local-factor identities equal
the canonical inverses in `selectedValue`; the executable controller need not
construct the same inverse expression syntactically.
-/

namespace SubexponentialSAT.SubexpCRTSelectedInput

open Polynomial SubexpLiftRing SubexpQuarticRing

noncomputable section

abbrev Coefficient (p D : ℕ) := SubexpPolynomialPowerProgram.Coefficient p (D+1)
abbrev Jet (p D : ℕ) := SubexpPolynomialPowerProgram.FixedPolynomial p (D+1) D

/-- Definitionally the selected-coefficient instance of the actual local
CRT decoder, without importing its execution proof. -/
def decode (p D : ℕ) [Fact p.Prime] (a : Coefficient p D) : SubexpActualRing.Ring p (D+1) :=
  quotientDenote (QuarticSearch.liftedCoefficients p (D+1))
    (a.map (wordValue p (D+1)))

/-- Definitionally the actual fixed-polynomial denotation. -/
def denote (p D : ℕ) [Fact p.Prime] (P : Jet p D) : Polynomial (SubexpActualRing.Ring p (D+1)) :=
  PolynomialAlgorithm.denote (P.val.map (decode p D))

variable {p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
  (S : Factor.System V F (ZMod p)) {c : SubexpLayoutSpec.Parameters p k Δ r tau}
  (L : SubexpLayoutSpec.Layout (E := SubexpActualRing.E p) S.toPattern c)

/-- The canonical scalar inverse used by the selected-layout reference. -/
def selectedInverse : Fin c.Q → SubexpActualRing.Ring p (Fintype.card V + 1) :=
  let μ := Fintype.card V + 1
  let A := SubexpCounting.selectedLiftedLayout S L μ (Nat.succ_pos _)
  let sectionLift := SubexpActualRing.residueSection p μ (Nat.succ_pos _)
  TruncatedInverse.constantInverse (Fintype.card V)
    (SubexpCounting.differenceInverse A sectionLift μ)

/-- The actual separated jet appearing in `selectedValue`. -/
def selectedJet : Fin c.Q → Polynomial (SubexpActualRing.Ring p (Fintype.card V + 1)) :=
  let μ := Fintype.card V + 1
  let A := SubexpCounting.selectedLiftedLayout S L μ (Nat.succ_pos _)
  let lift := SubexpActualRing.coordinateLift p μ
  let hlift := SubexpActualRing.rho_coordinateLift p μ (Nat.succ_pos _)
  let units := SubexpActualRing.coordinateLift_unitDifferences p μ
  let sectionLift := SubexpActualRing.residueSection p μ (Nat.succ_pos _)
  SubexpCounting.layoutJet A lift hlift sectionLift
    (GlobalPolynomial.interpolatedTable S lift units) μ (Fintype.card V)

omit [DecidableEq F] in
theorem selectedValue_eq : SubexpCRTAtZero.selectedValue S L =
    SubexpCRTAtZero.value (SubexpCRTAtZero.selectedNode S L) (Fintype.card V)
      (selectedInverse S L) (selectedJet S L) := rfl

omit [DecidableEq F] in
/-- All hypotheses of the canonical inverse identity follow from the actual
selected ring's nilpotence and residue kernel. No inverse is assumed. -/
theorem selectedInverse_correct (i : Fin c.Q) :
    selectedInverse S L i *
      (TruncatedInverse.localFactor (SubexpCRTAtZero.selectedNode S L)
        (Fintype.card V) i).coeff 0 = 1 := by
  let μ := Fintype.card V + 1
  let A := SubexpCounting.selectedLiftedLayout S L μ (Nat.succ_pos _)
  let sectionLift := SubexpActualRing.residueSection p μ (Nat.succ_pos _)
  exact TruncatedInverse.constantInverse_correct A.theta (Fintype.card V)
    (SubexpCounting.differenceInverse A sectionLift μ)
    (SubexpCounting.differenceInverse_mul A sectionLift μ
      (SubexpActualRing.prime_power_zero p μ)
      (SubexpActualRing.rho_ker p μ (Nat.succ_pos _))) i

omit [DecidableEq F] in
/-- Valid scalar inverses are unique, even when they came from a different
finite expression or from the concrete machine's geometric correction. -/
theorem selectedInverse_unique
    (a : Fin c.Q → SubexpActualRing.Ring p (Fintype.card V + 1))
    (ha : ∀ i, a i *
      (TruncatedInverse.localFactor (SubexpCRTAtZero.selectedNode S L)
        (Fintype.card V) i).coeff 0 = 1) :
    a = selectedInverse S L := by
  funext i
  let x := (TruncatedInverse.localFactor (SubexpCRTAtZero.selectedNode S L)
    (Fintype.card V) i).coeff 0
  apply inv_unique (x := x)
  · exact (mul_comm x (a i)).trans (ha i)
  · exact (mul_comm x (selectedInverse S L i)).trans (selectedInverse_correct S L i)

omit [DecidableEq F] in
/-- The generic CRT expression agrees with the selected-layout reference
under exactly the node and jet denotations read back from its inputs. -/
theorem value_eq_selected
    (θ : Fin c.Q → SubexpActualRing.Ring p (Fintype.card V + 1))
    (J : Fin c.Q → Polynomial (SubexpActualRing.Ring p (Fintype.card V + 1)))
    (a : Fin c.Q → SubexpActualRing.Ring p (Fintype.card V + 1))
    (hnodes : ∀ i, θ i = SubexpCRTAtZero.selectedNode S L i)
    (hjets : ∀ i, J i = selectedJet S L i)
    (ha : ∀ i, a i * (TruncatedInverse.localFactor θ (Fintype.card V) i).coeff 0 = 1) :
    SubexpCRTAtZero.value θ (Fintype.card V) a J = SubexpCRTAtZero.selectedValue S L := by
  have hθ : θ = SubexpCRTAtZero.selectedNode S L := funext hnodes
  have hJ : J = selectedJet S L := funext hjets
  have ha' : ∀ i, a i *
      (TruncatedInverse.localFactor (SubexpCRTAtZero.selectedNode S L)
        (Fintype.card V) i).coeff 0 = 1 := by
    simpa only [hθ] using ha
  rw [hθ, hJ, selectedInverse_unique S L a ha']
  exact (selectedValue_eq S L).symm

omit [DecidableEq F] in
/-- A caller may choose the canonical inverse family in the generic
execution theorem, with its validity proved from the node readback alone. -/
theorem selectedInverse_correct_of_nodes
    (nodes : Fin c.Q → Coefficient p (Fintype.card V))
    (hnodes : ∀ i, decode p (Fintype.card V) (nodes i) = SubexpCRTAtZero.selectedNode S L i)
    (i : Fin c.Q) :
    selectedInverse S L i *
      (TruncatedInverse.localFactor (fun j => decode p (Fintype.card V) (nodes j))
        (Fintype.card V) i).coeff 0 = 1 := by
  have hθ : (fun j => decode p (Fintype.card V) (nodes j)) =
      SubexpCRTAtZero.selectedNode S L := funext hnodes
  rw [hθ]
  exact selectedInverse_correct S L i

omit [DecidableEq F] in
/-- Specialize to the actual fixed-width coefficient and fixed-length jet
families consumed by `SubexpCRTOuterExecution.command_value/program_value`. -/
theorem represented_value_eq_selected
    (nodes : Fin c.Q → Coefficient p (Fintype.card V))
    (jets : Fin c.Q → Jet p (Fintype.card V))
    (a : Fin c.Q → SubexpActualRing.Ring p (Fintype.card V + 1))
    (hnodes : ∀ i, decode p (Fintype.card V) (nodes i) = SubexpCRTAtZero.selectedNode S L i)
    (hjets : ∀ i, denote p (Fintype.card V) (jets i) = selectedJet S L i)
    (ha : ∀ i, a i *
      (TruncatedInverse.localFactor (fun j => decode p (Fintype.card V) (nodes j))
        (Fintype.card V) i).coeff 0 = 1) :
    SubexpCRTAtZero.value (fun i => decode p (Fintype.card V) (nodes i)) (Fintype.card V) a
      (fun i => denote p (Fintype.card V) (jets i)) = SubexpCRTAtZero.selectedValue S L :=
  value_eq_selected S L _ _ a hnodes hjets ha

omit [DecidableEq F] in
/-- The concrete output-value theorem now concludes the selected reference;
the generic execution equality remains an explicit input to this bridge. -/
theorem output_value_eq_selected
    (nodes : Fin c.Q → Coefficient p (Fintype.card V))
    (jets : Fin c.Q → Jet p (Fintype.card V))
    (a : Fin c.Q → SubexpActualRing.Ring p (Fintype.card V + 1))
    (hnodes : ∀ i, decode p (Fintype.card V) (nodes i) = SubexpCRTAtZero.selectedNode S L i)
    (hjets : ∀ i, denote p (Fintype.card V) (jets i) = selectedJet S L i)
    (ha : ∀ i, a i *
      (TruncatedInverse.localFactor (fun j => decode p (Fintype.card V) (nodes j))
        (Fintype.card V) i).coeff 0 = 1)
    (b : Coefficient p (Fintype.card V))
    (hvalue : decode p (Fintype.card V) b =
      SubexpCRTAtZero.value (fun i => decode p (Fintype.card V) (nodes i)) (Fintype.card V) a
        (fun i => denote p (Fintype.card V) (jets i))) :
    decode p (Fintype.card V) b = SubexpCRTAtZero.selectedValue S L :=
  hvalue.trans (represented_value_eq_selected S L nodes jets a hnodes hjets ha)

end
end SubexponentialSAT.SubexpCRTSelectedInput

end OAI.Algorithms
