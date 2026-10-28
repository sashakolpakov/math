import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainMomentReadback
import OAI.Algorithms.SubexponentialSAT.SubexpNodeCanonicalJet

namespace OAI.Algorithms

/-! Canonical typed CRT jets have exactly the bytes established for the
actual node worker. These definitions are specifications of its output;
the executed collector is unchanged. -/

namespace SubexponentialSAT.SubexpMainCanonicalJetReadback

noncomputable section

open SubexpQuarticRing SubexpLiftRing SubexpLayoutSpec

variable (p D : ℕ) [Fact p.Prime]

local instance primePower_gt_one : Fact (1 < p^(D + 1)) :=
  ⟨SubexpQuarticEncoding.primePower_one_lt p (D + 1) (Nat.succ_pos D)⟩

def code (x : SubexpActualRing.Ring p (D + 1)) : SubexpCRTSelectedInput.Coefficient p D :=
  (SubexpQuarticEncoding.quotientCoefficients (QuarticSearch.liftedCoefficients p (D + 1)) x).map
    (encodeWord p (D + 1))

theorem code_decode (x : SubexpActualRing.Ring p (D + 1)) :
    SubexpCRTSelectedInput.decode p D (code p D x) = x := by
  unfold SubexpCRTSelectedInput.decode code
  simp only [Quad.map, wordValue_encodeWord]
  exact SubexpQuarticEncoding.quotientDenote_quotientCoefficients _ x

theorem code_word (x : SubexpActualRing.Ring p (D + 1)) :
    SubexpFlatAdd.encode (code p D x) =
      SubexpQuarticEncoding.encodeSelected p (D + 1) (Nat.succ_pos D) x := by
  simp only [code, SubexpFlatAdd.encode, SubexpFlatAdd.quadWords,
    SubexpFlatAdd.flatten, Quad.map, encodeWord, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.append_nil,
    SubexpQuarticEncoding.encodeSelected, SubexpQuarticEncoding.encodeQuotient,
    SubexpQuarticEncoding.encodeQuad, List.append_assoc]

def jetCode (theta : SubexpActualRing.Ring p (D + 1))
    (poly : Polynomial (SubexpActualRing.Ring p (D + 1))) : SubexpCRTSelectedInput.Jet p D :=
  ⟨(List.range D).map (fun j => code p D ((JetCRT.jet theta D poly).coeff j)), by simp⟩

theorem jetCode_decode (theta : SubexpActualRing.Ring p (D + 1))
    (poly : Polynomial (SubexpActualRing.Ring p (D + 1))) :
    SubexpCRTSelectedInput.denote p D (jetCode p D theta poly) = JetCRT.jet theta D poly := by
  simp only [SubexpCRTSelectedInput.denote, jetCode, List.map_map, Function.comp_def, code_decode]
  exact SubexpCountExecution.denote_jetCoefficientList D theta poly

theorem jetCode_word (theta : SubexpActualRing.Ring p (D + 1))
    (poly : Polynomial (SubexpActualRing.Ring p (D + 1))) :
    SubexpPolynomialPowerProgram.encode p (D + 1) (jetCode p D theta poly) =
      ((List.range D).map fun j =>
        SubexpQuarticEncoding.encodeSelected p (D + 1) (Nat.succ_pos D)
          ((JetCRT.jet theta D poly).coeff j)).flatten := by
  simp only [SubexpPolynomialPowerProgram.encode, SubexpConvolutionControl.encodeArray,
    jetCode, List.map_map, Function.comp_def, code_word]

section Selected

variable {p} {k Δ r : ℕ} {tau : ℚ}
  {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
  (S : Factor.System V F (ZMod p)) {c : Parameters p k Δ r tau}
  (L : Layout (E := SubexpActualRing.E p) S.toPattern c)

local notation "N" => Fintype.card V

def selectedCode (i : Fin c.Q) : SubexpCRTSelectedInput.Jet p N :=
  jetCode p N (SubexpCRTAtZero.selectedNode S L i)
    (SubexpMainMomentReadback.selectedPolynomial S L)

omit [DecidableEq F] in
theorem selectedCode_decode (i : Fin c.Q) :
    SubexpCRTSelectedInput.denote p N (selectedCode S L i) =
      SubexpCRTSelectedInput.selectedJet S L i :=
  (jetCode_decode p N _ _).trans (SubexpMainMomentReadback.selectedJet_eq S L i).symm

end Selected

section Native

variable {p D} {k Δ r : ℕ} {tau : ℚ}
  {F : Type*} [Fintype F] [DecidableEq F]
  (S : Factor.System (Fin D) F (ZMod p)) {c : Parameters p k Δ r tau}
  (L : Layout (E := SubexpActualRing.E p) S.toPattern c)

def table : ∀ e, MvPolynomial {v // v ∈ S.scope e} (SubexpActualRing.Ring p (D + 1)) :=
  GlobalPolynomial.interpolatedTable S (SubexpActualRing.coordinateLift p (D + 1))
    (SubexpActualRing.coordinateLift_unitDifferences p (D + 1))

omit [DecidableEq F] in
theorem selectedCode_word (i : Fin c.Q) :
    SubexpPolynomialPowerProgram.encode p (Fintype.card (Fin D) + 1) (selectedCode S L i) =
      SubexpNodeCanonicalJet.canonicalJetBytes L (table S) i := by
  rw [selectedCode, jetCode_word]
  let bytes (n : ℕ) : List Bool :=
    ((List.range n).map fun j =>
      SubexpQuarticEncoding.encodeSelected p (n + 1) (Nat.succ_pos n)
        ((JetCRT.jet
          ((SubexpExplicitLift.explicitLiftedLayout L (n + 1) (Nat.succ_pos n)).theta i) n
          (GlobalPolynomial.rowGlobalPolynomial
            (GlobalPolynomial.interpolatedTable S (SubexpActualRing.coordinateLift p (n + 1))
              (SubexpActualRing.coordinateLift_unitDifferences p (n + 1)))
            (SubexpExplicitLift.explicitLiftedLayout L (n + 1) (Nat.succ_pos n)).row
            (SubexpActualRing.coordinateLift p (n + 1)))).coeff j)).flatten
  change bytes (Fintype.card (Fin D)) = bytes D
  exact congrArg bytes (Fintype.card_fin D)

omit [DecidableEq F] in
theorem selectedCode_words :
    (List.ofFn (SubexpNodeCanonicalJet.canonicalJetBytes L (table S))).flatten =
      (List.finRange c.Q).flatMap (fun i =>
        SubexpPolynomialPowerProgram.encode p (Fintype.card (Fin D) + 1) (selectedCode S L i)) := by
  simp only [selectedCode_word, List.flatMap_def, ← List.ofFn_eq_map]

end Native

end
end SubexponentialSAT.SubexpMainCanonicalJetReadback

end OAI.Algorithms
