import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryWidthScalar
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramQuantitative

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Width
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram CostAssembly.Polynomial
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem packing_factors_eq (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k)) :
    (packingProblem q k hg).factors=(q.input k).factors := by
  unfold PackingCallerProgram.Problem.factors packingProblem
  rw [PackingIncidenceInput.Stats.native_factor_count]
  rfl

theorem packing_scalars (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (l : Fin 8 → ℕ) (V : ℕ) (hv : ∀i,(Execute.guardedModel (q.input k) l).val i ≤ V) :
    let p := packingProblem q k hg
    p.n ≤ V ∧ p.factors ≤ V ∧ p.incidences ≤ V ∧ p.r ≤ V ∧ p.Q ≤ V ∧ p.s ≤ V ∧
      p.r^p.Q ≤ V ∧ p.r^(2*p.Q) ≤ V ∧ (produce (q.input k)).R ≤ V := by
  have hn := hv 0
  have hf := hv 5
  have hi := hv 7
  have he0 : (Execute.guardedModel (q.input k) l).val 0=(q.input k).ambient := Execute.guardedModel_input (q.input k) l 0
  have he5 : (Execute.guardedModel (q.input k) l).val 5=(q.input k).factors := Execute.guardedModel_input (q.input k) l 5
  have he7 : (Execute.guardedModel (q.input k) l).val 7=(q.input k).incidences := Execute.guardedModel_input (q.input k) l 7
  rw [he0] at hn
  rw [he5] at hf
  rw [he7] at hi
  have hr := hv 18
  rw [Execute.guardedModel_radius] at hr
  obtain ⟨_,_,_,_,hQ,hs,hR,hN⟩ := Layout.model_core_values (q.input k) l
  have hQ' := hv 21
  have hs' := hv 25
  have hR' := hv 29
  have hN' := hv 31
  have heQ : (Execute.guardedModel (q.input k) l).val 21=(produce (q.input k)).Q :=
    (Execute.guardedModel_public (q.input k) l 4).trans hQ
  have heS : (Execute.guardedModel (q.input k) l).val 25=(produce (q.input k)).epsilonDen :=
    (Execute.guardedModel_public (q.input k) l 5).trans hs
  have heR : (Execute.guardedModel (q.input k) l).val 29=(produce (q.input k)).R :=
    (Execute.guardedModel_public (q.input k) l 6).trans hR
  have heN : (Execute.guardedModel (q.input k) l).val 31=(produce (q.input k)).N :=
    (Execute.guardedModel_public (q.input k) l 7).trans hN
  rw [heQ] at hQ'
  rw [heS] at hs'
  rw [heR] at hR'
  rw [heN] at hN'
  refine ⟨hn,?_,?_,hr,hQ',hs',?_,hN',hR'⟩
  · rw [packing_factors_eq]; exact hf
  · rw [packingProblem_incidences]; exact hi
  · change (produce (q.input k)).r ^ (produce (q.input k)).Q ≤ V
    apply le_trans _ hN'
    change (produce (q.input k)).r ^ (produce (q.input k)).Q ≤
      (produce (q.input k)).r ^ (2 * (produce (q.input k)).Q)
    exact Nat.pow_le_pow_right (by have := produce_r_ge_two (q.input k); omega) (by omega)

theorem packing_globalSize_le (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (a b : Data) (l : Fin 8 → ℕ) (bw : Bank.Words)
    (hs : FrontState q k a b l bw) (U V : ℕ)
    (hw : ∀i,(b.stacks i).length ≤ U) (hv : ∀i,(Execute.guardedModel (q.input k) l).val i ≤ V) :
    PackingCallerProgram.globalSize b (packingProblem q k hg) ≤ 780*U+9*V+2 := by
  obtain ⟨hn,hf,hi,hr,hQ,he,ha,ht,_⟩ := packing_scalars q k hg l V hv
  have hmass : PackingCallerProgram.inputMass b ≤ 768*U := by
    unfold PackingCallerProgram.inputMass
    calc
      _ ≤ ∑ _i : Fin 768,U := Finset.sum_le_sum (fun i _=>hw i)
      _ = _ := by simp
  have hscope := hw 718
  rw [hs.scopes] at hscope
  have hmask := hw 719
  rw [hs.forward] at hmask
  have h55 := hw 720
  have h56 := hw 709
  have h57 := hw 722
  have h58 := hw 723
  have h59 := hw 721
  unfold PackingCallerProgram.globalSize PackingCallerProgram.Bounds.scalarSize
  simp only [PackingCallerProgram.Wide.parameterStore, PackingCallerProgram.Wide.project]
  change _ ≤ _
  change (PackingIncidenceInput.Scan.scopeBits q.scopeRows).length ≤ U at hscope
  dsimp [packingProblem] at hn hf hi hr hQ he ha ht hscope hmask ⊢
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Width

end OAI.Algorithms
