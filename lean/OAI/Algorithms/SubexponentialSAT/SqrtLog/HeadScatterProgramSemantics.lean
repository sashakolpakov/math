import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgramScan

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram

private theorem write_eq_set (mask : List Bool) (j : ℕ) (bit : Bool) (hj : j < mask.length) :
    write mask j bit = mask.set j bit := by
  simp [List.set_eq_take_append_cons_drop, hj, write]

theorem scatter_outside (js : List ℕ) (bits mask : List Bool) (k : ℕ)
    (hb : ∀ j ∈ js, j < mask.length) (hk : k ∉ js) :
    (scatter js bits mask)[k]? = mask[k]? := by
  induction js generalizing bits mask with
  | nil => rfl
  | cons j js ih =>
      cases bits with
      | nil => rfl
      | cons b bits =>
          have hj := hb j (by simp)
          have hne : j ≠ k := by intro h; subst k; simp at hk
          have htail : k ∉ js := by intro h; exact hk (List.mem_cons_of_mem j h)
          have hw := write_length mask j b hj
          change (scatter js bits (write mask j b))[k]? = _
          rw [ih bits (write mask j b) (by intro l hl; rw [hw]; exact hb l (by simp [hl])) htail]
          rw [write_eq_set mask j b hj, List.getElem?_set_ne hne]

theorem scatter_at (js : List ℕ) (bits mask : List Bool) (k : ℕ) (bit : Bool)
    (hb : ∀ j ∈ js, j < mask.length) (hd : js.Nodup) (hm : (k, bit) ∈ js.zip bits) :
    (scatter js bits mask)[k]? = some bit := by
  induction js generalizing bits mask with
  | nil => simp at hm
  | cons j js ih =>
      cases bits with
      | nil => simp at hm
      | cons b bits =>
          have hj := hb j (by simp)
          have hw := write_length mask j b hj
          have htail : ∀ l ∈ js, l < (write mask j b).length := by
            intro l hl; rw [hw]; exact hb l (by simp [hl])
          simp only [List.zip_cons_cons, List.mem_cons] at hm
          rcases hm with heq | hm
          · have he : k = j ∧ bit = b := by simpa using heq
            rcases he with ⟨he1, he2⟩
            subst k; subst bit
            change (scatter js bits (write mask j b))[j]? = some b
            rw [scatter_outside js bits _ j htail (List.nodup_cons.mp hd).1]
            rw [write_eq_set mask j b hj, List.getElem?_set_self hj]
          · exact ih bits (write mask j b) htail (List.nodup_cons.mp hd).2 hm

/-- A full ambient mask. The empty head list still returns n zero bits. -/
def mask (n : ℕ) (js : List ℕ) (bits : List Bool) : List Bool :=
  scatter js bits (List.replicate n false)

theorem mask_length (n : ℕ) (js : List ℕ) (bits : List Bool)
    (hb : ∀ j ∈ js, j < n) : (mask n js bits).length = n := by
  simpa [mask] using scatter_length js bits (List.replicate n false) (by simpa using hb)

theorem mask_outside (n : ℕ) (js : List ℕ) (bits : List Bool) (k : ℕ)
    (hb : ∀ j ∈ js, j < n) (hk : k < n) (hne : k ∉ js) :
    (mask n js bits)[k]? = some false := by
  rw [mask, scatter_outside js bits _ k (by simpa using hb) hne]
  simp [hk]

theorem mask_at (n : ℕ) (js : List ℕ) (bits : List Bool) (k : ℕ) (bit : Bool)
    (hb : ∀ j ∈ js, j < n) (hd : js.Nodup) (hm : (k, bit) ∈ js.zip bits) :
    (mask n js bits)[k]? = some bit :=
  scatter_at js bits _ k bit (by simpa using hb) hd hm

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
