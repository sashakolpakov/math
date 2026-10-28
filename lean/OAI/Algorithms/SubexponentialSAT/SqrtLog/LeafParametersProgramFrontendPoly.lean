import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramNative

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds
open Circuit
noncomputable section

/-- A fixed ordinary polynomial in a declared input measure. -/
def Poly {α : Type*} (measure f : α → ℕ) : Prop :=
  ∃ C d : ℕ, ∀ a, f a ≤ C*(measure a)^d

namespace Poly
variable {α : Type*} {measure f g : α → ℕ}

theorem mono (hf : Poly measure f) (h : ∀ a, g a ≤ f a) : Poly measure g := by
  obtain ⟨C,d,hf⟩ := hf
  exact ⟨C,d,fun a => (h a).trans (hf a)⟩

theorem const (measure : α → ℕ) (C : ℕ) : Poly measure (fun _ => C) :=
  ⟨C,0,by intro a; simp⟩

theorem self (measure : α → ℕ) : Poly measure measure :=
  ⟨1,1,by intro a; simp⟩

theorem add (hmeasure : ∀ a,1 ≤ measure a) (hf : Poly measure f) (hg : Poly measure g) :
    Poly measure (fun a => f a+g a) := by
  obtain ⟨C,d,hf⟩ := hf
  obtain ⟨D,e,hg⟩ := hg
  refine ⟨C+D,d+e,?_⟩
  intro a
  have hd := Nat.pow_le_pow_right (hmeasure a) (show d ≤ d+e by omega)
  have he := Nat.pow_le_pow_right (hmeasure a) (show e ≤ d+e by omega)
  calc
    f a+g a ≤ C*(measure a)^d+D*(measure a)^e := Nat.add_le_add (hf a) (hg a)
    _ ≤ C*(measure a)^(d+e)+D*(measure a)^(d+e) :=
      Nat.add_le_add (Nat.mul_le_mul_left C hd) (Nat.mul_le_mul_left D he)
    _ = (C+D)*(measure a)^(d+e) := (Nat.add_mul _ _ _).symm

theorem mul (hf : Poly measure f) (hg : Poly measure g) :
    Poly measure (fun a => f a*g a) := by
  obtain ⟨C,d,hf⟩ := hf
  obtain ⟨D,e,hg⟩ := hg
  refine ⟨C*D,d+e,?_⟩
  intro a
  calc
    f a*g a ≤ (C*(measure a)^d)*(D*(measure a)^e) := Nat.mul_le_mul (hf a) (hg a)
    _ = (C*D)*(measure a)^(d+e) := by rw [pow_add]; ac_rfl

theorem pow (hf : Poly measure f) (k : ℕ) : Poly measure (fun a => f a^k) := by
  obtain ⟨C,d,hf⟩ := hf
  refine ⟨C^k,d*k,?_⟩
  intro a
  calc
    f a^k ≤ (C*(measure a)^d)^k := Nat.pow_le_pow_left (hf a) k
    _ = C^k*(measure a)^(d*k) := by rw [mul_pow,pow_mul]

theorem iter (hf : Poly measure f) (hpos : ∀ a,1 ≤ f a) (k : ℕ) :
    Poly measure (fun a => iterMajorant k (f a)) := by
  apply (mul (const measure (polynomialCoefficient k)) (pow hf (6^k))).mono
  intro a
  exact iterMajorant_polynomial k (f a) (hpos a)

theorem compose (hmeasure : ∀ a,1 ≤ measure a) (hf : Poly measure f)
    {g : ℕ → ℕ} (hg : Poly (fun B => B+1) g) : Poly measure (fun a => g (f a)) := by
  obtain ⟨C,d,hg⟩ := hg
  apply (mul (const measure C) (pow (add hmeasure hf (const measure 1)) d)).mono
  exact fun a => hg (f a)
end Poly

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds

end OAI.Algorithms
