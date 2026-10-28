import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramEntries
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramBlockEntries

namespace OAI.Algorithms

/-! A computable integer row for every incidence position. Inactive covered
positions and non-head uncovered positions are zero. Active rows are precisely
the raw block constraints, with repetitions and zero padding permitted. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking

variable {r Q : ℕ} {I O : Type*}
variable [Fintype I] [DecidableEq I] [CommRing O]

/-- This definition uses the executable packing lookup and scalar numerator.
The arbitrary finite equivalence used by the semantic layout is absent. -/
def paddedEntry (P : PackingData I (UniversalType r Q 1))
    (A R : ℕ) (t : Fin Q) (g : Fin r) (v w : I) : ℤ :=
  match P.lookup v with
  | none => if (P.label v).head t = g ∧ w = v then 1 else 0
  | some (j,u) => match P.lookup w with
    | none => 0
    | some (k,y) =>
      if j = k ∧ u ∈ joint t g (0 : Fin 1) ∧ y ∈ joint t g (0 : Fin 1) then
        (if u = y then (2 : ℤ)^(R-1) else 0) -
          LayoutCoefficientAlgorithm.scalarEntry (0 : Fin 1) t A R u y
      else 0

abbrev IncidenceHead (P : PackingData I (UniversalType r Q 1))
    (t : Fin Q) (g : Fin r) := {v : I // (P.label v).head t = g}

def paddedConstraint (P : PackingData I (UniversalType r Q 1))
    (A R : ℕ) (t : Fin Q) (g : Fin r) : I → IncidenceHead P t g → ℤ :=
  fun v w => paddedEntry P A R t g v w.val

omit [Fintype I] in
theorem paddedEntry_covered (P : PackingData I (UniversalType r Q 1))
    (A R : ℕ) (t : Fin Q) (g : Fin r)
    (j k : Fin P.blockCount) (u y : UniversalType r Q 1) :
    paddedEntry P A R t g (P.vertexAt j u) (P.vertexAt k y) =
      if j = k ∧ u ∈ joint t g (0 : Fin 1) ∧ y ∈ joint t g (0 : Fin 1) then
        (if u = y then (2 : ℤ)^(R-1) else 0) -
          LayoutCoefficientAlgorithm.scalarEntry (0 : Fin 1) t A R u y
      else 0 := by
  simp only [paddedEntry,P.lookup_at]

omit [Fintype I] in
theorem paddedConstraint_inactive (P : PackingData I (UniversalType r Q 1))
    (A R : ℕ) (t : Fin Q) (g : Fin r)
    (j : Fin P.blockCount) (u : UniversalType r Q 1)
    (hu : u ∉ joint t g (0 : Fin 1)) :
    paddedConstraint P A R t g (P.vertexAt j u) = 0 := by
  funext w
  simp only [paddedConstraint,paddedEntry,P.lookup_at]
  cases hw : P.lookup w.val with
  | none => rfl
  | some z => rcases z with ⟨k,y⟩; simp [hu]

omit [Fintype I] in
theorem paddedConstraint_uncovered_inactive
    (P : PackingData I (UniversalType r Q 1))
    (A R : ℕ) (t : Fin Q) (g : Fin r) (v : I)
    (hv : P.lookup v = none) (hg : (P.label v).head t ≠ g) :
    paddedConstraint P A R t g v = 0 := by
  funext w
  simp [paddedConstraint,paddedEntry,hv,hg]

variable {node : Fin Q → O}

omit [Fintype I] in
theorem paddedConstraint_covered_eq
    (P : PackingData I (UniversalType r Q 1))
    (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node)
    (t : Fin Q) (g : Fin r) (j : Fin P.blockCount)
    (u : Joint t g (0 : Fin 1)) :
    paddedConstraint P A R t g (P.vertexAt j u.val) =
      LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
        P.completeBlocks t g
        (.inl (j,(Fintype.equivFin (Joint t g (0 : Fin 1))) u)) := by
  classical
  let C := LayoutUniversal.data (r := r) A R denom hdenom units
  funext w
  change paddedEntry P A R t g (P.vertexAt j u.val) w.val = _
  by_cases hw : w.val ∈ Set.range P.completeBlocks.embed
  · obtain ⟨⟨k,y⟩,hy⟩ := hw
    have hyhead : y.head t = g := by
      have hhead : (P.label (P.completeBlocks.embed (k,y))).head t = g := by
        rw [hy]
        exact w.property
      simpa only [P.completeBlocks_apply,P.label_at] using hhead
    let yy : LayoutUniversal.Head t g := ⟨y, hyhead⟩
    have he : LayoutBlocks.embedHead (LayoutUniversal.data (r := r) A R denom hdenom units)
        P.completeBlocks t g k yy = w :=
      Subtype.ext hy
    have hb := blockConstraint_covered
      (C := LayoutUniversal.data (r := r) A R denom hdenom units)
      (P := P) (t := t) (g := g) j k
      ((Fintype.equivFin (Joint t g (0 : Fin 1))) u) yy
    have hbw : LayoutBlocks.constraints (LayoutUniversal.data (r := r) A R denom hdenom units)
        P.completeBlocks t g (.inl (j, (Fintype.equivFin (Joint t g (0 : Fin 1))) u)) w =
        if j = k then (LayoutUniversal.data (r := r) A R denom hdenom units).constraints
          t g ((Fintype.equivFin (Joint t g (0 : Fin 1))) u) yy else 0 := by
      rw [← he]
      exact hb
    rw [hbw, ← hy]
    change paddedEntry P A R t g (P.vertexAt j u.val) (P.vertexAt k y) = _
    have hc : C.constraints t g
        ((Fintype.equivFin (Joint t g (0 : Fin 1))) u) yy =
        LayoutUniversal.constraints A R t g u yy := by
      simp [C, LayoutUniversal.data, Layout.ofIndexed]
    by_cases hj : j = k
    · subst k
      rw [ite_eq_left rfl]
      rw [paddedEntry_covered]
      calc
        (if j = j ∧ u.val ∈ joint t g (0 : Fin 1) ∧ y ∈ joint t g (0 : Fin 1) then
            (if u.val = y then (2 : ℤ) ^ (R - 1) else 0) -
              LayoutCoefficientAlgorithm.scalarEntry (0 : Fin 1) t A R u.val y
          else 0) = headEntry A R t g u yy := by
            simp [headEntry, u.property, yy, hyhead]
        _ = LayoutUniversal.constraints A R t g u yy := headEntry_eq A R t g u yy
        _ = C.constraints t g ((Fintype.equivFin (Joint t g (0 : Fin 1))) u) yy := hc.symm
    · rw [paddedEntry_covered]
      simp [hj]
  · rw [blockConstraint_uncovered C P t g j
        ((Fintype.equivFin (Joint t g (0 : Fin 1))) u) w hw]
    have hn := (P.lookup_none_iff w.val).mpr hw
    simp [paddedEntry,P.lookup_at,hn]

omit [Fintype I] in
theorem paddedConstraint_uncovered_eq
    (P : PackingData I (UniversalType r Q 1))
    (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node)
    (t : Fin Q) (g : Fin r) (v : IncidenceHead P t g)
    (hv : v.val ∉ Set.range P.completeBlocks.embed) :
    paddedConstraint P A R t g v.val =
      LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
        P.completeBlocks t g (.inr ⟨v,hv⟩) := by
  classical
  funext w
  have hs := singletonConstraint
    (C := LayoutUniversal.data (r := r) A R denom hdenom units)
    (P := P) (t := t) (g := g) ⟨v, hv⟩ w
  change paddedEntry P A R t g v.val w.val = _
  rw [hs]
  have hn := (P.lookup_none_iff v.val).mpr hv
  simp [paddedEntry,hn,v.property]

omit [Fintype I] in
/-- Every old raw constraint has an actual incidence position representing it. -/
theorem paddedConstraint_cover
    (P : PackingData I (UniversalType r Q 1))
    (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node)
    (t : Fin Q) (g : Fin r)
    (a : LayoutBlocks.RowIndex (LayoutUniversal.data A R denom hdenom units)
      P.completeBlocks t g) :
    ∃ v, paddedConstraint P A R t g v =
      LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
        P.completeBlocks t g a := by
  classical
  rcases a with ⟨j,a⟩ | v
  · let u := (Fintype.equivFin (Joint t g (0 : Fin 1))).symm a
    refine ⟨P.vertexAt j u.val,?_⟩
    have h := paddedConstraint_covered_eq P A R denom hdenom units t g j u
    have hu : (Fintype.equivFin (Joint t g (0 : Fin 1))) u = a :=
      (Fintype.equivFin (Joint t g (0 : Fin 1))).apply_symm_apply a
    rw [hu] at h
    exact h
  · exact ⟨v.val.val,paddedConstraint_uncovered_eq P A R denom hdenom units t g
      v.val v.property⟩

omit [Fintype I] in
/-- Every emitted row is either zero or one of the old raw constraints. -/
theorem paddedConstraint_shape
    (P : PackingData I (UniversalType r Q 1))
    (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node)
    (t : Fin Q) (g : Fin r) (v : I) :
    paddedConstraint P A R t g v = 0 ∨
      ∃ a, paddedConstraint P A R t g v =
        LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
          P.completeBlocks t g a := by
  classical
  cases hv : P.lookup v with
  | none =>
    by_cases hg : (P.label v).head t = g
    · exact Or.inr ⟨.inr ⟨⟨v,hg⟩,(P.lookup_none_iff v).mp hv⟩,
        paddedConstraint_uncovered_eq P A R denom hdenom units t g ⟨v,hg⟩
          ((P.lookup_none_iff v).mp hv)⟩
    · exact Or.inl (paddedConstraint_uncovered_inactive P A R t g v hv hg)
  | some z =>
    rcases z with ⟨j,u⟩
    have he := P.lookup_sound v (j,u) hv
    rw [← he]
    by_cases hu : u ∈ joint t g (0 : Fin 1)
    · exact Or.inr ⟨.inl (j,(Fintype.equivFin (Joint t g (0 : Fin 1))) ⟨u,hu⟩),
        paddedConstraint_covered_eq P A R denom hdenom units t g j ⟨u,hu⟩⟩
    · exact Or.inl (paddedConstraint_inactive P A R t g j u hu)

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
