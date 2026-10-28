import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramSemantics

namespace OAI.Algorithms

/-! Total original-coordinate source family computed by the native controller.
The missing-incidence branch is zero; required factor-scope incidences use
the exact packed row selected by the actual plan lookup. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

def sourceRowFamily {A : Type*} [AddMonoid A] (ps : List (ℕ × ℕ))
    (ambient factor literal : ℕ) (source : ℕ → ℕ → A) (owner : ℕ) : A :=
  if (literal,ambient+factor) ∈ ps then
    ownerSum ps owner (source (ps.idxOf (literal,ambient+factor)))
  else 0

theorem sourceRowFamily_present {A : Type*} [AddMonoid A] (ps : List (ℕ × ℕ))
    (ambient factor literal : ℕ) (source : ℕ → ℕ → A) (owner : ℕ)
    (h : (literal,ambient+factor) ∈ ps) :
    sourceRowFamily ps ambient factor literal source owner=
      ownerSum ps owner (source (ps.idxOf (literal,ambient+factor))) := by
  simp [sourceRowFamily,h]

theorem sourceRowFamily_absent {A : Type*} [AddMonoid A] (ps : List (ℕ × ℕ))
    (ambient factor literal : ℕ) (source : ℕ → ℕ → A) (owner : ℕ)
    (h : (literal,ambient+factor) ∉ ps) :
    sourceRowFamily ps ambient factor literal source owner=0 := by
  simp [sourceRowFamily,h]

theorem sourceRowFamily_pullback {A : Type*} [AddCommMonoid A] {n : ℕ}
    (ps : Fin n → ℕ × ℕ) (ambient factor literal : ℕ) (source : ℕ → ℕ → A)
    (owner : ℕ) (row : Fin n)
    (hmem : (literal,ambient+factor) ∈ List.ofFn ps)
    (hlookup : (List.ofFn ps).idxOf (literal,ambient+factor)=row.val) :
    sourceRowFamily (List.ofFn ps) ambient factor literal source owner=
      LayoutPullback.row (fun i : Fin n => (ps i).1) (fun i => source row.val i.val) owner := by
  rw [sourceRowFamily_present _ _ _ _ _ _ hmem,hlookup]
  exact ownerSum_pullback ps owner (source row.val)

theorem sourceRowFamily_degree {A : Type*} [CommRing A] (ps : List (ℕ × ℕ))
    (ambient factor literal : ℕ) (source : ℕ → ℕ → Polynomial A) (owner R : ℕ)
    (h : ∀ row col, (source row col).natDegree ≤ R) :
    (sourceRowFamily ps ambient factor literal source owner).natDegree ≤ R := by
  unfold sourceRowFamily
  split_ifs
  · exact ownerSum_degree ps owner _ R (fun i _ => h _ i)
  · simp

theorem sourceRowFamily_full {A : Type*} [CommRing A] (ps : List (ℕ × ℕ))
    (ambient factor literal : ℕ) (source : ℕ → ℕ → Polynomial A) (owner R : ℕ)
    (h : ∀ row col, (source row col).natDegree ≤ R) :
    Truncation.trunc (R+1) (sourceRowFamily ps ambient factor literal source owner)=
      sourceRowFamily ps ambient factor literal source owner :=
  trunc_full_degree _ R (sourceRowFamily_degree ps ambient factor literal source owner R h)

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
