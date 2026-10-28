import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeRestore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeCount

namespace OAI.Algorithms

/-! The exact reusable branch frame, beyond the protected-input projection. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native
open SubexponentialSAT BitProgram StructuredCalls
open LeafNodeSamplesProgram
attribute [local simp] Fin.coe_ofNat_eq_mod
noncomputable section

private theorem countPrepare_265 :
    (265 : Fin 768) ∉ Count.Prepare.ports := by
  apply Count.Prepare.protected_not_mem
  simp [Count.Prepare.protectedInputs]

attribute [local irreducible] Count.Prepare.ports

def branchedStacks (a : Data) (high jet : List Bool) : Fin 768 → List Bool :=
  Function.update (Function.update (Function.update a.stacks 702 (a.stacks 338).reverse)
    703 (HighIncidenceProgram.Restriction.zeroMerge (a.stacks 338) high).reverse) 265 jet

 theorem sampled_high_stacks (a : Data) (rh : Fin 4 → Bool) (high : List Bool)
    (nodes : ℕ → List Bool) {Q : ℕ} (jets : Fin Q → List Bool) (rr : Fin 40 → Bool)
    (hhigh : ∀ i∈LeafHighContextProgram.changed,a.stacks i=[])
    (h190 : a.stacks 190=[]) (h191 : a.stacks 191=[])
    (hb : ∀ i∈collectorBlankPorts,
      (Samples.prepared (LeafHighContextProgram.finished a rh high)).stacks i=[])
    (hn : ((List.finRange Q).map (fun i => nodes i.val)).flatten=a.stacks 256) :
    (sampled (LeafHighContextProgram.finished a rh high) nodes jets rr).stacks=
      branchedStacks a high ((List.finRange Q).map jets).flatten := by
  let b := LeafHighContextProgram.finished a rh high
  have hbp : (Samples.prepared b).stacks=b.stacks := sample_prepare_stacks b
    ((LeafHighContextProgram.finished_frame a rh high 190 (by decide)).trans h190)
    ((LeafHighContextProgram.finished_frame a rh high 191 (by decide)).trans h191)
  have hout := collector_final_stacks (Samples.prepared b) nodes jets hb
  have hn' : ((List.finRange Q).map (fun i => nodes i.val)).flatten=b.stacks 256 :=
    hn.trans (LeafHighContextProgram.finished_frame a rh high 256 (by decide)).symm
  rw [hbp,hn',Function.update_eq_self] at hout
  change (sampled b nodes jets rr).stacks=_
  rw [show (sampled b nodes jets rr).stacks=Function.update b.stacks 265
    ((List.finRange Q).map jets).flatten from by simpa only [sampled,state,hbp] using hout,high_stacks a rh high hhigh]
  rfl

 theorem branched_prepared (a b : Data) (high jet : List Bool)
    (hb : b.stacks=branchedStacks a high jet)
    (he : ∀ i∈Count.Prepare.ports,a.stacks i=[]) (h699 : a.stacks 699=[]) :
    (Count.Prepare.output b).stacks=b.stacks := by
  apply count_prepare_stacks b
  · intro i hi
    have hi265 : i≠265 := by intro h; subst i; exact countPrepare_265 hi
    have hl := Count.Prepare.ports_lt i hi
    have hi702 : i≠702 := by intro h; subst i; norm_num at hl
    have hi703 : i≠703 := by intro h; subst i; norm_num at hl
    rw [hb]
    simp only [branchedStacks,Function.update_of_ne hi265,
      Function.update_of_ne hi702,Function.update_of_ne hi703]
    exact he i hi
  · rw [hb]
    simpa [branchedStacks] using h699

 theorem finalStacks_restored (a b : Data) (high jet word : List Bool)
    (hb : b.stacks=branchedStacks a high jet)
    (he : ∀ i∈Count.Prepare.ports,a.stacks i=[]) (h699 : a.stacks 699=[])
    (h265 : a.stacks 265=[]) (h702 : a.stacks 702=[]) (h703 : a.stacks 703=[]) :
    finalStacks b word=Function.update a.stacks 323 word := by
  unfold finalStacks
  rw [branched_prepared a b high jet hb he h699,hb]
  funext i
  by_cases h1 : i=265
  · subst i; simp [branchedStacks,h265]
  by_cases h2 : i=702
  · subst i; simp [branchedStacks,h702]
  by_cases h3 : i=703
  · subst i; simp [branchedStacks,h703]
  by_cases h4 : i=323
  · subst i; simp [branchedStacks]
  simp [branchedStacks,h1,h2,h3,h4]

end
end SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native

end OAI.Algorithms
