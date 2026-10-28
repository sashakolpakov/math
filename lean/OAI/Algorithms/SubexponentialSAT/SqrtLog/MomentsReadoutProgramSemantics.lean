import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgramNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramNormalize
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsOutput

namespace OAI.Algorithms

/-! Identification of the physically computed coefficient list with the
sparse moment readout. The only lookup premise is normalized distinct keys. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram.Dictionary
open scoped BigOperators

variable {R : Type*} [CommRing R]

theorem addFetched_denote {K : Type*} [DecidableEq K]
    (p e : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p e)
    (cache : RingProgram.ScalarCache p e) (scalar : ZMod (p^e) →+* R)
    {d : ℕ} (basis : Fin d → R)
    (entries : List (K × RingProgram.Code (Word (baseWidth p e)) d)) (k : K)
    (acc : RingProgram.Code (Word (baseWidth p e)) d)
    (hn : (Squarefree.Sparse.keys entries).Nodup) :
    let f := RingProgram.denote (RingProgram.scalarRing p e M cache) scalar basis
    f (addFetched p e M cache entries k acc) =
      f acc + Squarefree.Sparse.fetch k (denoteTable f entries) := by
  dsimp only
  let f := RingProgram.denote (RingProgram.scalarRing p e M cache) scalar basis
  have hf := Squarefree.Program.fetch_eq_lookup (denoteTable f entries) k
    (by simpa only [denoteTable_keys] using hn)
  rw [denoteTable_lookup] at hf
  change f (addFetched p e M cache entries k acc) =
    f acc + Squarefree.Sparse.fetch k (denoteTable f entries)
  cases he : entries.lookup k with
  | none =>
      have hz : Squarefree.Sparse.fetch k (denoteTable f entries)=0 := by simpa [he] using hf
      simp [addFetched,he,hz]
  | some x =>
      have hx : Squarefree.Sparse.fetch k (denoteTable f entries)=f x := by simpa [he] using hf
      simpa only [addFetched,he,hx,RingProgram.scalarRing_program] using
        RingProgram.denote_add (RingProgram.scalarRing p e M cache) scalar basis acc x

theorem foldU_denote {n d : ℕ} (p e : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
    (scalar : ZMod (p^e) →+* R) (basis : Fin d → R)
    (entries : List (Squarefree.Index (Fin n) × RingProgram.Code (Word (baseWidth p e)) d))
    (z u k : ℕ) (acc : RingProgram.Code (Word (baseWidth p e)) d)
    (hn : (Squarefree.Sparse.keys entries).Nodup) :
    let f := RingProgram.denote (RingProgram.scalarRing p e M cache) scalar basis
    f (foldU p e M cache entries z u k acc) = f acc+
      ∑ i ∈ Finset.range k, Squarefree.Sparse.fetch ⟨u+i,z,∅⟩ (denoteTable f entries) := by
  dsimp only
  induction k generalizing u acc with
  | zero => simp [foldU]
  | succ k ih =>
      rw [foldU,ih,addFetched_denote p e M cache scalar basis entries _ _ hn]
      simp [Finset.sum_range_succ',
        add_assoc,add_comm,add_left_comm]

theorem outputCodes_denote_shift {n d : ℕ} (p e : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
    (scalar : ZMod (p^e) →+* R) (basis : Fin d → R)
    (entries : List (Squarefree.Index (Fin n) × RingProgram.Code (Word (baseWidth p e)) d))
    (t : ℕ) (zero : RingProgram.Code (Word (baseWidth p e)) d) (z J : ℕ)
    (hn : (Squarefree.Sparse.keys entries).Nodup)
    (hz : RingProgram.denote (RingProgram.scalarRing p e M cache) scalar basis zero=0) :
    let f := RingProgram.denote (RingProgram.scalarRing p e M cache) scalar basis
    (outputCodes p e M cache entries t zero z J).map f =
      Moments.tabulate J (fun j => ∑ u ∈ Finset.range t,
        Squarefree.Sparse.fetch ⟨u,z+j,∅⟩ (denoteTable f entries)) := by
  dsimp only
  induction J generalizing z with
  | zero => rfl
  | succ J ih =>
      simp only [outputCodes,List.map_cons,Moments.tabulate]
      rw [foldU_denote p e M cache scalar basis entries z 0 t zero hn,ih,hz]
      simp [Nat.add_comm,Nat.add_left_comm]

theorem outputCodes_denote {n d : ℕ} (p e : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
    (scalar : ZMod (p^e) →+* R) (basis : Fin d → R)
    (entries : List (Squarefree.Index (Fin n) × RingProgram.Code (Word (baseWidth p e)) d))
    (t J : ℕ) (zero : RingProgram.Code (Word (baseWidth p e)) d)
    (hn : (Squarefree.Sparse.keys entries).Nodup)
    (hz : RingProgram.denote (RingProgram.scalarRing p e M cache) scalar basis zero=0) :
    let f := RingProgram.denote (RingProgram.scalarRing p e M cache) scalar basis
    (outputCodes p e M cache entries t zero 0 J).map f =
      Moments.outputCoefficients t J (denoteTable f entries) := by
  simpa [Moments.outputCoefficients] using
    outputCodes_denote_shift p e M cache scalar basis entries t zero 0 J hn hz

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram

end OAI.Algorithms
