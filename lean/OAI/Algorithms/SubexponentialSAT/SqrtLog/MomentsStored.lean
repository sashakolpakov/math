import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsSparse

namespace OAI.Algorithms

/-! The actual normalized sparse representation used by the head loops.
Proof fields erase at execution; every operation is a finite list operation.
The associated costs count ring operations and key scans. -/

namespace SubexponentialSAT.SqrtLog.Moments

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

structure Stored (vars : Finset V) (t J : ℕ) where
  data : Sparse.Data (Index V) R
  valid : Sparse.ValidData vars t J data
  nodup : (Sparse.keys data).Nodup

namespace Stored

variable {vars : Finset V} {t J : ℕ}

noncomputable def denote (a : Stored (R := R) vars t J) : Jet V R := Sparse.denote a.data

theorem canonical (a : Stored (R := R) vars t J) :
    Squarefree.canonical t J a.denote = a.denote := a.valid.canonical

omit [CommSemiring R] in
theorem length_le (a : Stored (R := R) vars t J) :
    a.data.length ≤ t * J * (Sparse.supportUniverse vars J).card := a.valid.length_le a.nodup

def zero : Stored (R := R) vars t J :=
  ⟨[], by simp [Sparse.ValidData, Sparse.keys], by simp [Sparse.keys]⟩

def one : Stored (R := R) vars t J :=
  ⟨Sparse.one t J, Sparse.constant_valid vars t J 1,
    by by_cases h : 0 < t ∧ 0 < J <;> simp [Sparse.one, Sparse.constant, h, Sparse.keys]⟩

def add (a b : Stored (R := R) vars t J) : Stored (R := R) vars t J :=
  ⟨Sparse.add a.data b.data, a.valid.add b.valid, Sparse.nodup_normalize _⟩

def mul (a b : Stored (R := R) vars t J) : Stored (R := R) vars t J :=
  ⟨Sparse.mul t J a.data b.data, a.valid.mul b.valid, Sparse.mul_nodup _ _ _ _⟩

def scale (c : R) (a : Stored (R := R) vars t J) : Stored (R := R) vars t J :=
  ⟨Sparse.scale c a.data, a.valid.scale c, by simpa using a.nodup⟩

def project (s : Finset V) (a : Stored (R := R) vars t J) : Stored (R := R) vars t J :=
  ⟨sparseProject s a.data, (rawProject_valid s a.data a.valid).normalize,
    Sparse.nodup_normalize _⟩

def ops : MomentsAlgorithm.Ops R (Finset V) (Stored (R := R) vars t J) where
  zero := zero
  one := one
  add a b := (add a b, Sparse.normalizeWork (a.data ++ b.data))
  mul a b := (mul a b, Sparse.mulWork t J a.data b.data)
  scale c a := (scale c a, a.data.length)
  project s a := (project s a, a.data.length + Sparse.normalizeWork (rawProject s a.data))

theorem ops_correct : MomentsAlgorithm.CanonicalCorrect
    (ops (R := R) (vars := vars) (t := t) (J := J)) denote ringScalar projectSupport
      (Squarefree.canonical t J) where
  idempotent := canonical_idempotent t J
  mul_normal := Squarefree.canonical_mul t J
  project_normal s a := by
    rw [projectSupport_canonical, canonical_idempotent]
  zero := rfl
  one := Sparse.denote_one t J
  add a b := by
    change Sparse.denote (Sparse.add a.data b.data) = _
    rw [Sparse.denote_add, map_add, a.canonical, b.canonical]
    rfl
  mul a b := Sparse.denote_mul t J a.data b.data
  scale c a := by
    change Sparse.denote (Sparse.scale c a.data) = _
    dsimp only [denote]
    rw [ringScalar_eq_atom, ← Sparse.denote_scale]
    exact (a.valid.scale c).canonical.symm
  project s a := by
    change Sparse.denote (sparseProject s a.data) = _
    dsimp only [denote]
    rw [← denote_sparseProject]
    exact (rawProject_valid s a.data a.valid).normalize.canonical.symm

def sizeBound (vars : Finset V) (t J : ℕ) : ℕ :=
  t * J * (Sparse.supportUniverse vars J).card

theorem add_cost (a b : Stored (R := R) vars t J) :
    (ops.add a b).2 ≤ 2 * sizeBound vars t J * (2 * sizeBound vars t J + 1) := by
  let L := sizeBound vars t J
  have ha : a.data.length ≤ L := a.length_le
  have hb : b.data.length ≤ L := b.length_le
  have hu := Sparse.indexUniverse_card_le vars t J
  have hn := Sparse.normalizeWork_le (a.data ++ b.data) (Sparse.indexUniverse vars t J) (by
    intro q hq
    have h : q ∈ Sparse.keys a.data ∨ q ∈ Sparse.keys b.data := by
      simpa [Sparse.keys] using hq
    exact h.elim (a.valid.in_universe q) (b.valid.in_universe q))
  change Sparse.normalizeWork (a.data ++ b.data) ≤ _
  refine hn.trans (Nat.mul_le_mul ?_ ?_)
  · simp only [List.length_append]; change a.data.length + b.data.length ≤ 2 * L; omega
  · change 2 * (Sparse.indexUniverse vars t J).card + 1 ≤ 2 * L + 1
    change (Sparse.indexUniverse vars t J).card ≤ L at hu
    omega

theorem mul_cost (a b : Stored (R := R) vars t J) :
    (ops.mul a b).2 ≤ sizeBound vars t J ^ 2 * (2 * sizeBound vars t J + 2) := by
  have h := Sparse.mulWork_le a.valid b.valid
  have hu := Sparse.indexUniverse_card_le vars t J
  refine h.trans (Nat.mul_le_mul ?_ ?_)
  · simpa [sizeBound, pow_two] using Nat.mul_le_mul a.length_le b.length_le
  · dsimp [sizeBound]
    omega

theorem scale_cost (c : R) (a : Stored (R := R) vars t J) :
    (ops.scale c a).2 ≤ sizeBound vars t J := a.length_le

theorem project_cost (s : Finset V) (a : Stored (R := R) vars t J) :
    (ops.project s a).2 ≤ sizeBound vars t J * (2 * sizeBound vars t J + 2) := by
  let L := sizeBound vars t J
  have ha : a.data.length ≤ L := a.length_le
  have hr := rawProject_length_le s a.data
  have hu : (Sparse.indexUniverse vars t J).card ≤ L := Sparse.indexUniverse_card_le vars t J
  have hn := Sparse.normalizeWork_le (rawProject s a.data) (Sparse.indexUniverse vars t J)
    (rawProject_valid s a.data a.valid).in_universe
  have hmul : (rawProject s a.data).length * (2 * (Sparse.indexUniverse vars t J).card + 1) ≤
      L * (2 * L + 1) := Nat.mul_le_mul (hr.trans ha) (by omega)
  change a.data.length + Sparse.normalizeWork (rawProject s a.data) ≤ _
  calc
    _ ≤ L + L * (2 * L + 1) := Nat.add_le_add ha (hn.trans hmul)
    _ = L * (2 * L + 2) := by ring

/-- Concrete M-support loop bound; with L=tJM its highest M power is four.
N counts local bucket assignments (summed over heads), H counts heads.
The cost of constructing each local factor jet is separately charged. -/
theorem run_cost (data : Finset V → List (List (R × Stored (R := R) vars t J)))
    (supports : List (Finset V)) (N H : ℕ)
    (hN : ∀ s ∈ supports, MomentsAlgorithm.entries (data s) ≤ N)
    (hH : ∀ s ∈ supports, (data s).length ≤ H) :
    (MomentsAlgorithm.run ops data supports).2 ≤
      supports.length * (N * (sizeBound vars t J +
        2 * sizeBound vars t J * (2 * sizeBound vars t J + 1)) +
        H * (sizeBound vars t J ^ 2 * (2 * sizeBound vars t J + 2)) +
        sizeBound vars t J * (2 * sizeBound vars t J + 2) +
        2 * sizeBound vars t J * (2 * sizeBound vars t J + 1)) := by
  exact MomentsAlgorithm.run_cost_uniform ops _ _ _ _ add_cost mul_cost scale_cost project_cost
    data supports N H hN hH

end Stored
end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
