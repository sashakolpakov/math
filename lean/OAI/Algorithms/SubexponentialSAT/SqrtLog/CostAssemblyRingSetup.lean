import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyRingBounds

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly.RingSetup
open LeafRingSetupProgram LeafParametersProgram CostAssembly.Polynomial

private theorem numberEnvelope_ordinary : Ordinary numberEnvelope := by
  unfold numberEnvelope serializationEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const (workPorts++outputPorts).length) (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 3))) (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 3)) (ordinary_add (ordinary_mul (ordinary_const 7) ordinary_id) (ordinary_const 5))) (ordinary_mul (ordinary_const 20) (ordinary_add ordinary_id (ordinary_const 1)))) (ordinary_mul (ordinary_const 20) (ordinary_add ordinary_id (ordinary_const 1)))) (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 3))) (ordinary_mul (ordinary_const 100) (ordinary_pow (ordinary_add (ordinary_add ordinary_id ordinary_id) (ordinary_const 1)) 2))) (ordinary_const 1))) (ordinary_mul (ordinary_const 5) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 7) ordinary_id) (ordinary_const 6)) (ordinary_mul (ordinary_mul (ordinary_const 32) (ordinary_add ordinary_id (ordinary_const 1))) (ordinary_add ordinary_id (ordinary_const 1)))))) (ordinary_add (ordinary_mul (ordinary_const 7) ordinary_id) (ordinary_const 8))) (ordinary_const 32))

private theorem coreEnvelope_ordinary : Ordinary coreEnvelope := by
  unfold coreEnvelope scalarBudget
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2001) (ordinary_pow (ordinary_add (ordinary_add ordinary_id ordinary_id) (ordinary_const 2)) 2)) (ordinary_mul (ordinary_const 500000) (ordinary_pow (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 3) ordinary_id) ordinary_id) (ordinary_const 1)) 3))) (ordinary_const 1)) (ordinary_add (ordinary_mul (ordinary_const 7) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_const 8))) (ordinary_const 32)) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 3) (ordinary_mul (ordinary_const searchCoefficient) (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) 10))) (ordinary_mul (ordinary_const 7) (ordinary_mul (ordinary_const 2) ordinary_id))) (ordinary_mul ordinary_id (ordinary_add (ordinary_mul (ordinary_const 28) ordinary_id) (ordinary_const 14)))) (ordinary_const 15))) (ordinary_add (ordinary_mul (ordinary_const 7) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_const 8))) (ordinary_mul (ordinary_mul (ordinary_const 208000) (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) 5)) (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) 2)))

private theorem constants_ordinary {f g h : ℕ → ℕ}
    (hf : Ordinary f) (hg : Ordinary g) (hh : Ordinary h) :
    Ordinary (fun S => constantsBudget (f S) (g S) (h S)) := by
  unfold constantsBudget LeafProgram.Constants.budget
  exact (ordinary_add (ordinary_add (ordinary_mul (ordinary_const constantStartPorts.length) (ordinary_add (ordinary_mul (ordinary_const 2) hf) (ordinary_const 3))) (ordinary_mul (ordinary_const 3) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 7) hg) (ordinary_const 8)) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul hh (ordinary_add (ordinary_mul (ordinary_const 22) hg) (ordinary_const 25))) (ordinary_mul (ordinary_const 4) hg)) (ordinary_const 16)) (ordinary_const 1))))) (ordinary_mul (ordinary_const constantAliases.length) (ordinary_add (ordinary_mul (ordinary_const 9) (ordinary_add (ordinary_add hf (ordinary_add (ordinary_mul (ordinary_const constantStartPorts.length) (ordinary_add (ordinary_mul (ordinary_const 2) hf) (ordinary_const 3))) (ordinary_mul (ordinary_const 3) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 7) hg) (ordinary_const 8)) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul hh (ordinary_add (ordinary_mul (ordinary_const 22) hg) (ordinary_const 25))) (ordinary_mul (ordinary_const 4) hg)) (ordinary_const 16)) (ordinary_const 1)))))) (ordinary_const 2))) (ordinary_const 8))))

private theorem nodes_ordinary {f g h j : ℕ → ℕ}
    (hf : Ordinary f) (hg : Ordinary g) (hh : Ordinary h) (hj : Ordinary j) :
    Ordinary (fun S => nodesBudget (f S) (g S) (h S) (j S)) := by
  unfold nodesBudget RingNodeProgram.budget RingNodeProgram.stepBudget
  simp only [RingProgram.ternary_baseWidth]
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const nodesStartPorts.length) (ordinary_add (ordinary_mul (ordinary_const 2) hf) (ordinary_const 3))) (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_mul (ordinary_const 9) hf) (ordinary_const 8)))) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 8) hf) (ordinary_const 8)) (ordinary_mul hj (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul hh (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 100) (ordinary_pow (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) hg) hf) (ordinary_const 1)) 2)) (ordinary_mul (ordinary_const 14) (ordinary_mul (ordinary_const 2) hg))) (ordinary_mul (ordinary_const 8) hf)) (ordinary_const 19))) (ordinary_mul (ordinary_const 25) hf)) (ordinary_mul (ordinary_const 7) hh)) (ordinary_const 35)) (ordinary_const 1)))) (ordinary_const 5))) (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_mul (ordinary_const 7) (ordinary_mul hj (ordinary_mul hh (ordinary_mul (ordinary_const 2) hg)))) (ordinary_const 8)))) (ordinary_add (ordinary_mul hj (ordinary_add (ordinary_mul (ordinary_const 28) (ordinary_mul hh (ordinary_mul (ordinary_const 2) hg))) (ordinary_const 33))) (ordinary_const 11)))

private theorem idempotent_ordinary {f g : ℕ → ℕ}
    (hf : Ordinary f) (hg : Ordinary g) :
    Ordinary (fun S => idempotentEnvelope (f S) (g S)) := by
  unfold idempotentEnvelope IdempotentProgram.polynomialBudget
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const idempotentStartPorts.length) (ordinary_add (ordinary_mul (ordinary_const 2) hg) (ordinary_const 3))) (ordinary_add (ordinary_mul (ordinary_const 7) hg) (ordinary_const 8))) (ordinary_const 32)) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 100000000) (ordinary_pow (ordinary_add (ordinary_add hf hg) (ordinary_const 2)) 4)) (ordinary_mul (ordinary_mul (ordinary_const 7) hf) (ordinary_mul (ordinary_mul (ordinary_const 41000) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 3) hf) (ordinary_const 1)) 3)) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 2) hf) (ordinary_const 1)) 2)))) (ordinary_mul (ordinary_add hf (ordinary_const 1)) (ordinary_add (ordinary_mul (ordinary_const 16) (ordinary_add hg (ordinary_const 1))) (ordinary_const 16)))) (ordinary_const 2))) (ordinary_add (ordinary_mul (ordinary_const 7) (ordinary_mul (ordinary_const 6) (ordinary_pow hf 2))) (ordinary_const 8)))

theorem polynomialEnvelope_ordinary : Ordinary polynomialEnvelope := by
  have h0 := numberEnvelope_ordinary
  have h1 := coreEnvelope_ordinary
  have hw1 := ordinary_add (ordinary_add (ordinary_add ordinary_id h0) h1) (ordinary_const 1)
  have h2 := constants_ordinary hw1 (ordinary_mul (ordinary_const 2) ordinary_id) ordinary_id
  have hw2 := ordinary_add (ordinary_add hw1 h2) (ordinary_const 1)
  have h3 := nodes_ordinary hw2 ordinary_id ordinary_id ordinary_id
  have hw3 := ordinary_add (ordinary_add hw2 h3) (ordinary_const 1)
  have h4 := idempotent_ordinary ordinary_id hw3
  have hw4 := ordinary_add (ordinary_add hw3 h4) (ordinary_const 1)
  have hsum := ordinary_add (ordinary_add (ordinary_add (ordinary_add h0 h1) h2) h3) h4
  have htail := ordinary_mul (ordinary_const finalDiscard.length)
    (ordinary_add (ordinary_mul (ordinary_const 2) hw4) (ordinary_const 3))
  exact ordinary_add (ordinary_add hsum htail) (ordinary_const 32)

theorem producerBudget_ordinary : ∃ C d : ℕ,
    ∀ (m : Circuit.Model) (initialWidth V bankWidth S : ℕ),
      initialWidth ≤ S → V ≤ S → bankWidth ≤ S → (∀ i, m.len i ≤ S) →
      m.val 33 ≤ S → m.val 34 ≤ S → m.val 21 ≤ S →
      3^(m.val 34) ≤ 16*(m.val 21+1)^2 →
      producerBudget m initialWidth V bankWidth ≤ C*(S+1)^d := by
  obtain ⟨C,d,h⟩ := polynomialEnvelope_ordinary
  exact ⟨C,d,fun m i V W S hi hv hw hl ht hd hq hf =>
    (producerBudget_le m i V W S hi hv hw hl ht hd hq hf).trans (h S)⟩

end SubexponentialSAT.SqrtLog.CostAssembly.RingSetup

end OAI.Algorithms
