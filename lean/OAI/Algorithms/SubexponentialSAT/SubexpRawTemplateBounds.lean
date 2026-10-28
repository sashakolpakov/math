import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateGroupLoop
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateOuter
import OAI.Algorithms.SubexponentialSAT.Subexp.SupportSelectionData

namespace OAI.Algorithms

/-! Generated-byte and assembly-loop bounds for the actual raw template.
The outer/inner bank bundle supplies both entry counts and payload lengths.
Selector execution is charged separately by the enclosing controller. -/

namespace SubexponentialSAT.SubexpRawTemplateBounds

open SubexpRawTemplate

abbrev encode (xs : List Word) : Word := Encoding.encodeList id xs

def bankMaster (bases : List Word) (inners : List (List Word)) : Word :=
  encode (encode bases :: inners.map encode)

def groups (support factors : ℕ → Word) (inners : List (List Word)) : List Word :=
  inners.mapIdx (fun i xs => groupBytes (support i) (factors i) xs)

def output (outside : Word) (support factors : ℕ → Word)
    (bases : List Word) (inners : List (List Word)) : Word :=
  blocksBytes outside (encode (groups support factors inners)) bases

/-- Sum of the published concrete group and outer loop bounds. The parent
controller adds its selector, setup, group-framing and cleanup instructions. -/
def coreAssemblyCost (outside : Word) (support factors : ℕ → Word)
    (bases : List Word) (inners : List (List Word)) : ℕ :=
  (inners.mapIdx (fun i xs => groupCost (support i) (factors i) xs)).sum +
    outerCost outside (encode (groups support factors inners)) bases

theorem encoded_length (xs : List Word) :
    (encode xs).length = 2 * (xs.map List.length).sum + 2 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [encode, Encoding.length_encodeList_cons, id_eq,
        List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
      omega

private theorem sum_affine {α : Type*} (xs : List α) (f : α → ℕ) (a b : ℕ) :
    (xs.map (fun x => a * f x + b)).sum = a * (xs.map f).sum + b * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

theorem termBytes_length (x s f : Word) :
    (termBytes x s f).length = 2*x.length + 2*s.length + 2*f.length + 3 := by
  simp only [termBytes, List.length_append, Encoding.length_frame]
  omega

theorem termCost_eq (x s f : Word) :
    termCost x s f = 45*x.length + 34*s.length + 34*f.length + 85 := by
  rw [termCost, termBytes_length]
  ring

theorem groupBytes_length (s f : Word) (xs : List Word) :
    (groupBytes s f xs).length =
      4*(xs.map List.length).sum + (4*s.length+4*f.length+8)*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change (Encoding.encodeList (fun x => termBytes x s f) (x::xs)).length = _
      rw [Encoding.length_encodeList_cons, termBytes_length]
      change 2*(2*x.length+2*s.length+2*f.length+3)+2+(groupBytes s f xs).length = _
      rw [ih]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      ring

theorem groupCost_eq (s f : Word) (xs : List Word) :
    groupCost s f xs =
      57*(xs.map List.length).sum + (46*s.length+46*f.length+111)*xs.length+10 := by
  unfold groupCost scanBudget
  simp only [termCost_eq, groupBytes_length]
  have h : (xs.map (fun x => 45*x.length+34*s.length+34*f.length+85+2)).sum =
      45*(xs.map List.length).sum + (34*s.length+34*f.length+87)*xs.length := by
    simpa only [Nat.add_assoc] using
      sum_affine xs List.length 45 (34*s.length+34*f.length+87)
  rw [h]
  ring

theorem groupBytes_le (s f : Word) (xs : List Word) :
    (groupBytes s f xs).length ≤ 4*(s.length+f.length+1)*(encode xs).length := by
  rw [groupBytes_length, encoded_length]
  ring_nf
  omega

theorem groupCost_le (s f : Word) (xs : List Word) :
    groupCost s f xs ≤ 100*(s.length+f.length+1)*(encode xs).length := by
  rw [groupCost_eq, encoded_length]
  ring_nf
  omega

theorem blockBytes_length (x o g : Word) :
    (blockBytes x o g).length = 2*x.length+2*o.length+g.length+2 := by
  simp only [blockBytes, List.length_append, Encoding.length_frame]
  omega

theorem blockCost_eq (x o g : Word) :
    blockCost x o g = 45*x.length+34*o.length+23*g.length+73 := by
  rw [blockCost, blockBytes_length]
  ring

theorem blocksBytes_length (o g : Word) (xs : List Word) :
    (blocksBytes o g xs).length =
      4*(xs.map List.length).sum + (4*o.length+2*g.length+6)*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change (Encoding.encodeList (fun x => blockBytes x o g) (x::xs)).length = _
      rw [Encoding.length_encodeList_cons, blockBytes_length]
      change 2*(2*x.length+2*o.length+g.length+2)+2+(blocksBytes o g xs).length = _
      rw [ih]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      ring

theorem outerCost_eq (o g : Word) (xs : List Word) :
    outerCost o g xs =
      57*(xs.map List.length).sum + (46*o.length+29*g.length+93)*xs.length+10 := by
  unfold outerCost scanBudget
  simp only [blockCost_eq, blocksBytes_length]
  have h : (xs.map (fun x => 45*x.length+34*o.length+23*g.length+73+2)).sum =
      45*(xs.map List.length).sum + (34*o.length+23*g.length+75)*xs.length := by
    simpa only [Nat.add_assoc] using
      sum_affine xs List.length 45 (34*o.length+23*g.length+75)
  rw [h]
  ring

theorem blocksBytes_le (o g : Word) (xs : List Word) :
    (blocksBytes o g xs).length ≤ 4*(o.length+g.length+1)*(encode xs).length := by
  rw [blocksBytes_length, encoded_length]
  ring_nf
  omega

theorem outerCost_le (o g : Word) (xs : List Word) :
    outerCost o g xs ≤ 100*(o.length+g.length+1)*(encode xs).length := by
  rw [outerCost_eq, encoded_length]
  ring_nf
  omega

private theorem map_mapIdx {α β γ : Type*} (xs : List α) (f : ℕ → α → β) (g : β → γ) :
    (xs.mapIdx f).map g = xs.mapIdx (fun i x => g (f i x)) := by
  simp only [List.mapIdx_eq_zipIdx_map, List.map_map, Function.comp_def]

private theorem sum_mapIdx_le {α : Type*} (xs : List α) (f : ℕ → α → ℕ)
    (measure : α → ℕ) (K : ℕ) (h : ∀ i x, f i x ≤ K*measure x) :
    (xs.mapIdx f).sum ≤ K*(xs.map measure).sum := by
  induction xs generalizing f with
  | nil => simp
  | cons x xs ih =>
      have hh := h 0 x
      have ht := ih (fun i x => f (i+1) x) (fun i x => h (i+1) x)
      simp only [List.mapIdx_cons, List.sum_cons, List.map_cons]
      nlinarith

theorem bankMaster_length (bases : List Word) (inners : List (List Word)) :
    (bankMaster bases inners).length = 2*(encode bases).length +
      2*(inners.map (fun xs => (encode xs).length)).sum + 2*inners.length+3 := by
  unfold bankMaster
  rw [encoded_length]
  simp only [List.map_cons, List.sum_cons, List.length_cons, List.length_map,
    List.map_map, Function.comp_def]
  ring

theorem bankMaster_pos (bases : List Word) (inners : List (List Word)) :
    1 ≤ (bankMaster bases inners).length := by rw [bankMaster_length]; omega

theorem groups_encoded_le (support factors : ℕ → Word) (inners : List (List Word))
    (bases : List Word) (S F : ℕ)
    (hs : ∀ i, (support i).length ≤ S) (hf : ∀ i, (factors i).length ≤ F) :
    (encode (groups support factors inners)).length ≤
      4*(S+F+1)*(bankMaster bases inners).length := by
  have hsum : ((groups support factors inners).map List.length).sum ≤
      4*(S+F+1)*(inners.map (fun xs => (encode xs).length)).sum := by
    rw [groups, map_mapIdx]
    apply sum_mapIdx_le
    intro i xs
    exact (groupBytes_le (support i) (factors i) xs).trans (by gcongr; exact hs i; exact hf i)
  dsimp only [groups] at hsum
  rw [encoded_length, groups, List.length_mapIdx, bankMaster_length]
  ring_nf at hsum ⊢
  omega

theorem groupCosts_le (support factors : ℕ → Word) (inners : List (List Word))
    (bases : List Word) (S F : ℕ)
    (hs : ∀ i, (support i).length ≤ S) (hf : ∀ i, (factors i).length ≤ F) :
    (inners.mapIdx (fun i xs => groupCost (support i) (factors i) xs)).sum ≤
      100*(S+F+1)*(bankMaster bases inners).length := by
  have hsum : (inners.mapIdx (fun i xs => groupCost (support i) (factors i) xs)).sum ≤
      100*(S+F+1)*(inners.map (fun xs => (encode xs).length)).sum := by
    apply sum_mapIdx_le
    intro i xs
    exact (groupCost_le (support i) (factors i) xs).trans (by gcongr; exact hs i; exact hf i)
  have hb : (inners.map (fun xs => (encode xs).length)).sum ≤
      (bankMaster bases inners).length := by rw [bankMaster_length]; omega
  exact hsum.trans (Nat.mul_le_mul_left _ hb)

private theorem aggregate_le (outside : Word) (support factors : ℕ → Word)
    (bases : List Word) (inners : List (List Word)) (S F O : ℕ)
    (hs : ∀ i, (support i).length ≤ S) (hf : ∀ i, (factors i).length ≤ F)
    (ho : outside.length ≤ O) :
    outside.length + (encode (groups support factors inners)).length+1 ≤
      5*(S+F+O+1)*(bankMaster bases inners).length := by
  have hg := groups_encoded_le support factors inners bases S F hs hf
  have hb := bankMaster_pos bases inners
  nlinarith [Nat.zero_le ((S+F)*(bankMaster bases inners).length),
    Nat.mul_le_mul_left (O+1) hb]

theorem output_length_le (outside : Word) (support factors : ℕ → Word)
    (bases : List Word) (inners : List (List Word)) (S F O : ℕ)
    (hs : ∀ i, (support i).length ≤ S) (hf : ∀ i, (factors i).length ≤ F)
    (ho : outside.length ≤ O) :
    (output outside support factors bases inners).length ≤
      20*(S+F+O+1)*(bankMaster bases inners).length^2 := by
  have ha := aggregate_le outside support factors bases inners S F O hs hf ho
  have hb : (encode bases).length ≤ (bankMaster bases inners).length := by
    rw [bankMaster_length]; omega
  apply (blocksBytes_le outside (encode (groups support factors inners)) bases).trans
  calc
    _ ≤ 4*(5*(S+F+O+1)*(bankMaster bases inners).length)*(bankMaster bases inners).length := by gcongr
    _ = _ := by ring

theorem coreAssemblyCost_le (outside : Word) (support factors : ℕ → Word)
    (bases : List Word) (inners : List (List Word)) (S F O : ℕ)
    (hs : ∀ i, (support i).length ≤ S) (hf : ∀ i, (factors i).length ≤ F)
    (ho : outside.length ≤ O) :
    coreAssemblyCost outside support factors bases inners ≤
      600*(S+F+O+1)*(bankMaster bases inners).length^2 := by
  have ha := aggregate_le outside support factors bases inners S F O hs hf ho
  have hb : (encode bases).length ≤ (bankMaster bases inners).length := by
    rw [bankMaster_length]; omega
  have hout : outerCost outside (encode (groups support factors inners)) bases ≤
      500*(S+F+O+1)*(bankMaster bases inners).length^2 := by
    apply (outerCost_le outside (encode (groups support factors inners)) bases).trans
    calc
      _ ≤ 100*(5*(S+F+O+1)*(bankMaster bases inners).length)*(bankMaster bases inners).length := by gcongr
      _ = _ := by ring
  have hg := groupCosts_le support factors inners bases S F hs hf
  have hsq : (bankMaster bases inners).length ≤ (bankMaster bases inners).length^2 := by
    have hp := bankMaster_pos bases inners
    nlinarith
  have hgroup : (inners.mapIdx (fun i xs => groupCost (support i) (factors i) xs)).sum ≤
      100*(S+F+O+1)*(bankMaster bases inners).length^2 := by
    exact hg.trans (Nat.mul_le_mul
      (Nat.mul_le_mul_left 100 (by omega : S+F+1 ≤ S+F+O+1)) hsq)
  unfold coreAssemblyCost
  nlinarith

theorem selectedIndexBytes_le (test : ℕ → Bool) (D : ℕ) :
    (encode (Subexp.SupportSelectionProgram.indexWords test D)).length ≤ 2*(D+1)^2 := by
  have hc := Subexp.SupportSelectionProgram.indexWords_length_le test D
  have hw : ∀ w ∈ Subexp.SupportSelectionProgram.indexWords test D, (id w).length ≤ D := by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    have hiD : i < D := List.mem_range.mp (List.mem_filter.mp hi).1
    simpa only [id_eq, Subexp.SupportSelectionProgram.unary, List.length_replicate] using
      Nat.le_of_lt hiD
  have hb := Encoding.length_encodeList_upper id
    (Subexp.SupportSelectionProgram.indexWords test D) D hw
  change (encode (Subexp.SupportSelectionProgram.indexWords test D)).length ≤ _ at hb
  nlinarith

def selectedFactors {α : Type*} (payload : α → Word) (keep : ℕ → α → Bool)
    (items : List α) (g : ℕ) : Word :=
  encode ((items.filter (keep g)).map payload)

/-- Stable filtering never increases the serialized packet-master length. -/
theorem selectedFactors_length_le {α : Type*} (payload : α → Word)
    (keep : ℕ → α → Bool) (items : List α) (g : ℕ) :
    (selectedFactors payload keep items g).length ≤ (encode (items.map payload)).length := by
  induction items with
  | nil => exact le_rfl
  | cons x xs ih =>
      cases hx : keep g x <;>
        simp [selectedFactors, hx, encode, Encoding.length_encodeList_cons] at ih ⊢ <;> omega

def selectedSupport {D r Q Δ : ℕ}
    (P : Subexp.ConstructivePacking.PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (g : ℕ) : Word :=
  encode (Subexp.SupportSelectionProgram.indexWords
    (Subexp.SupportSelectionProgram.colorTest P t g) D)

def selectedOutside {D r Q Δ : ℕ}
    (P : Subexp.ConstructivePacking.PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ)) : Word :=
  encode (Subexp.SupportSelectionProgram.indexWords
    (Subexp.SupportSelectionProgram.outsideTest P) D)

private theorem input_polynomial (C B F D : ℕ) :
    C*(2*(D+1)^2+F+2*(D+1)^2+1)*B^2 ≤
      (5*C)*(B+F+D+1)^4 := by
  let N := B+F+D+1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hD : D+1 ≤ N := by dsimp [N]; omega
  have hF : F+1 ≤ N := by dsimp [N]; omega
  have hB : B ≤ N := by dsimp [N]; omega
  have hN2 : N ≤ N^2 := by nlinarith
  have hD2 := Nat.pow_le_pow_left hD 2
  have hB2 := Nat.pow_le_pow_left hB 2
  have hW : 2*(D+1)^2+F+2*(D+1)^2+1 ≤ 5*N^2 := by omega
  calc
    _ ≤ C*(5*N^2)*N^2 := by gcongr
    _ = _ := by dsimp [N]; ring

/-- The actual support selector and stable packet filter discharge every
payload-size bound. There is no hypothesis about the generated output. -/
theorem selected_output_length_le {α : Type*} {D r Q Δ : ℕ}
    (P : Subexp.ConstructivePacking.PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (payload : α → Word) (keep : ℕ → α → Bool) (items : List α)
    (bases : List Word) (inners : List (List Word)) :
    (output (selectedOutside P) (selectedSupport P t) (selectedFactors payload keep items)
      bases inners).length ≤
      100*((bankMaster bases inners).length+(encode (items.map payload)).length+D+1)^4 := by
  apply (output_length_le (selectedOutside P) (selectedSupport P t)
    (selectedFactors payload keep items) bases inners (2*(D+1)^2)
    (encode (items.map payload)).length (2*(D+1)^2)
    (fun i => selectedIndexBytes_le _ D) (fun i => selectedFactors_length_le payload keep items i)
    (selectedIndexBytes_le _ D)).trans
  simpa using input_polynomial 20 (bankMaster bases inners).length
    (encode (items.map payload)).length D

/-- Fixed degree four for the concrete group and outer assembly loops,
after substituting the real selected support and factor-packet byte lists. -/
theorem selected_coreAssemblyCost_le {α : Type*} {D r Q Δ : ℕ}
    (P : Subexp.ConstructivePacking.PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (payload : α → Word) (keep : ℕ → α → Bool) (items : List α)
    (bases : List Word) (inners : List (List Word)) :
    coreAssemblyCost (selectedOutside P) (selectedSupport P t) (selectedFactors payload keep items)
      bases inners ≤
      3000*((bankMaster bases inners).length+(encode (items.map payload)).length+D+1)^4 := by
  apply (coreAssemblyCost_le (selectedOutside P) (selectedSupport P t)
    (selectedFactors payload keep items) bases inners (2*(D+1)^2)
    (encode (items.map payload)).length (2*(D+1)^2)
    (fun i => selectedIndexBytes_le _ D) (fun i => selectedFactors_length_le payload keep items i)
    (selectedIndexBytes_le _ D)).trans
  simpa using input_polynomial 600 (bankMaster bases inners).length
    (encode (items.map payload)).length D

end SubexponentialSAT.SubexpRawTemplateBounds

end OAI.Algorithms
