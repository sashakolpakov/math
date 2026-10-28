import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbedding
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsStored

namespace OAI.Algorithms

/-! Padding a sparse dictionary preserves its exact coefficients, key
uniqueness, validity, and list length. The ambient bit representation need
not compact or renumber the residual variables. -/
namespace SubexponentialSAT.SqrtLog.ResidualEmbedding

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
variable {V W R : Type*} [DecidableEq V] [DecidableEq W] [CommSemiring R]

def index (e : V ↪ W) (a : Index V) : Index W := ⟨a.u, a.z, a.vars.map e⟩

omit [DecidableEq V] [DecidableEq W] in
theorem index_injective (e : V ↪ W) : Function.Injective (index e) := by
  intro a b h
  have hu := congrArg Index.u h
  have hz := congrArg Index.z h
  have hs := Finset.map_injective e (congrArg Index.vars h)
  cases a; cases b
  simp_all [index]

@[simp] theorem index_join (e : V ↪ W) (a b : Index V) :
    index e (a.join b) = (index e a).join (index e b) := by
  simp [index, Index.join, Finset.map_union]

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem index_kept (e : V ↪ W) (a : Index V) (t J : ℕ) :
    (index e a).Kept t J ↔ a.Kept t J := Iff.rfl

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem index_valid (e : V ↪ W) (a : Index V) :
    (index e a).Valid ↔ a.Valid := by simp [Index.Valid, index]

def data (e : V ↪ W) (l : Sparse.Data (Index V) R) : Sparse.Data (Index W) R :=
  l.map (fun a => (index e a.1, a.2))

omit [DecidableEq V] [DecidableEq W] [CommSemiring R] in
@[simp] theorem data_length (e : V ↪ W) (l : Sparse.Data (Index V) R) :
    (data e l).length = l.length := List.length_map _

omit [DecidableEq V] [DecidableEq W] [CommSemiring R] in
@[simp] theorem data_keys (e : V ↪ W) (l : Sparse.Data (Index V) R) :
    Sparse.keys (data e l) = (Sparse.keys l).map (index e) := by
  simp [data, Sparse.keys, List.map_map, Function.comp_def]

omit [DecidableEq V] [DecidableEq W] [CommSemiring R] in
theorem data_nodup (e : V ↪ W) (l : Sparse.Data (Index V) R)
    (hl : (Sparse.keys l).Nodup) : (Sparse.keys (data e l)).Nodup := by
  rw [data_keys]
  exact List.Nodup.map (index_injective e) hl

omit [DecidableEq V] [DecidableEq W] [CommSemiring R] in
theorem data_valid (e : V ↪ W) {vars : Finset V} {t J : ℕ}
    {l : Sparse.Data (Index V) R} (hl : Sparse.ValidData vars t J l) :
    Sparse.ValidData (vars.map e) t J (data e l) := by
  intro a ha
  rw [data_keys] at ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hk, hv, hs⟩ := hl b hb
  exact ⟨hk, (index_valid e b).mpr hv, Finset.map_subset_map.mpr hs⟩

noncomputable section

@[simp] theorem jet_atom (e : V ↪ W) (a : Index V) (c : R) :
    jet e (Sparse.atom a c) = Sparse.atom (index e a) c := by
  simp [jet, Sparse.atom, index]

@[simp] theorem denote_data (e : V ↪ W) (l : Sparse.Data (Index V) R) :
    Sparse.denote (data e l) = jet e (Sparse.denote l) := by
  induction l with
  | nil => simp [data, Sparse.denote, Sparse.decode]
  | cons a l ih =>
      simp only [data, List.map_cons, Sparse.denote, Sparse.decode, map_add, jet_atom]
      exact congrArg (Sparse.atom (index e a.1) a.2 + ·) ih

def stored (e : V ↪ W) {vars : Finset V} {t J : ℕ}
    (a : Moments.Stored (R := R) vars t J) : Moments.Stored (R := R) (vars.map e) t J :=
  ⟨data e a.data, data_valid e a.valid, data_nodup e a.data a.nodup⟩

@[simp] theorem denote_stored (e : V ↪ W) {vars : Finset V} {t J : ℕ}
    (a : Moments.Stored (R := R) vars t J) :
    (stored e a).denote = jet e a.denote := denote_data e a.data

/-- Enlarging only the validity envelope does not alter any stored bit data. -/
def weaken {vars vars' : Finset V} {t J : ℕ} (h : vars ⊆ vars')
    (a : Moments.Stored (R := R) vars t J) : Moments.Stored (R := R) vars' t J :=
  ⟨a.data, fun q hq => let hq' := a.valid q hq
      ⟨hq'.1, hq'.2.1, hq'.2.2.trans h⟩, a.nodup⟩

@[simp] theorem denote_weaken {vars vars' : Finset V} {t J : ℕ} (h : vars ⊆ vars')
    (a : Moments.Stored (R := R) vars t J) : (weaken h a).denote = a.denote := rfl

omit [DecidableEq V] [CommSemiring R] in
/-- The stronger, free-coordinate validity invariant remains available even
when a caller stores the dictionary in a full ambient validity envelope. -/
theorem weaken_data_valid {vars vars' : Finset V} {t J : ℕ} (h : vars ⊆ vars')
    (a : Moments.Stored (R := R) vars t J) :
    Sparse.ValidData vars t J (weaken h a).data := a.valid

end
end SubexponentialSAT.SqrtLog.ResidualEmbedding

end OAI.Algorithms
