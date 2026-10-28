import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyMoment

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly.Polynomial

/-- A closure predicate used only to certify that the displayed envelope is
a fixed polynomial, independently of the runtime model. -/
def Ordinary (f : ℕ → ℕ) : Prop := ∃ C d : ℕ, ∀ S, f S ≤ C*(S+1)^d

theorem ordinary_const (a : ℕ) : Ordinary (fun _ => a) := by
  exact ⟨a,0,by simp⟩

theorem ordinary_id : Ordinary (fun S => S) := by
  exact ⟨1,1,by intro S; simp⟩

theorem ordinary_add {f g : ℕ → ℕ} (hf : Ordinary f) (hg : Ordinary g) :
    Ordinary (fun S => f S+g S) := by
  obtain ⟨C,d,hf⟩ := hf
  obtain ⟨K,e,hg⟩ := hg
  refine ⟨C+K,d+e,?_⟩
  intro S
  have hd : (S+1)^d ≤ (S+1)^(d+e) := Nat.pow_le_pow_right (by omega) (by omega)
  have he : (S+1)^e ≤ (S+1)^(d+e) := Nat.pow_le_pow_right (by omega) (by omega)
  calc
    _ ≤ C*(S+1)^d+K*(S+1)^e := Nat.add_le_add (hf S) (hg S)
    _ ≤ C*(S+1)^(d+e)+K*(S+1)^(d+e) := by gcongr
    _ = _ := by ring

theorem ordinary_mul {f g : ℕ → ℕ} (hf : Ordinary f) (hg : Ordinary g) :
    Ordinary (fun S => f S*g S) := by
  obtain ⟨C,d,hf⟩ := hf
  obtain ⟨K,e,hg⟩ := hg
  refine ⟨C*K,d+e,?_⟩
  intro S
  calc
    _ ≤ (C*(S+1)^d)*(K*(S+1)^e) := Nat.mul_le_mul (hf S) (hg S)
    _ = _ := by rw [pow_add]; ring

theorem ordinary_pow {f : ℕ → ℕ} (hf : Ordinary f) (e : ℕ) :
    Ordinary (fun S => (f S)^e) := by
  obtain ⟨C,d,hf⟩ := hf
  refine ⟨C^e,d*e,?_⟩
  intro S
  calc
    _ ≤ (C*(S+1)^d)^e := Nat.pow_le_pow_left (hf S) e
    _ = _ := by rw [mul_pow,pow_mul]

end SubexponentialSAT.SqrtLog.CostAssembly.Polynomial

end OAI.Algorithms
