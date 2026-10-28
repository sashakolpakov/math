import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramConcreteFinite

namespace OAI.Algorithms

/-! The actual Cartesian order is a duplicate-free full finite enumeration
of dependent attained-label tuples. Finalizer reversal is retained exactly. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete
open MomentsAssembly

theorem appendOne_injective : Function.Injective
    (fun p : List HeadInput × HeadInput=>p.1++[p.2]) := by
  intro a b he
  have hr := congrArg List.reverse he
  have hh : a.2=b.2 ∧ a.1=b.1 := by
    simpa only [List.reverse_append,List.reverse_singleton,List.singleton_append,
      List.cons.injEq,List.reverse_inj] using hr
  exact Prod.ext hh.2 hh.1

theorem extend_nodup (rows : List (List HeadInput)) (choices : List HeadInput)
    (hr : rows.Nodup) (hc : choices.Nodup) : (extend rows choices).Nodup := by
  have hh := (hr.product hc).map appendOne_injective
  rw [extend,List.nodup_reverse]
  simpa [List.product,SProd.sprod,List.map_flatMap,List.map_map,Function.comp_def] using hh

theorem enumerateFrom_nodup (tables : List HeadTable) (rows : List (List HeadInput))
    (ht : ∀ table∈tables,table.choices.Nodup) (hr : rows.Nodup) :
    (enumerateFrom tables rows).Nodup := by
  induction tables generalizing rows with
  | nil => exact hr
  | cons table tables ih =>
      exact ih (extend rows table.choices) (fun t hm=>ht t (by simp [hm]))
        (extend_nodup rows table.choices hr (ht table (by simp)))

theorem enumerate_nodup (tables : List HeadTable)
    (ht : ∀ table∈tables,table.choices.Nodup) : (enumerate tables).Nodup :=
  enumerateFrom_nodup tables [[]] ht (by simp)

def tupleHeads {r : ℕ} {Y : Fin r → Type*}
    (input : ∀ g,Y g→HeadInput) (y : ∀ g,Y g) : List HeadInput :=
  List.ofFn (fun g=>input g (y g))

theorem tupleHeads_injective {r : ℕ} {Y : Fin r → Type*}
    (input : ∀ g,Y g→HeadInput) (hi : ∀ g,Function.Injective (input g)) :
    Function.Injective (tupleHeads input) := by
  intro a b he
  have hh := List.ofFn_injective he
  funext g
  exact hi g (congrFun hh g)

theorem tupleHeads_mem_iff {r : ℕ} (tables : Fin r → HeadTable) {Y : Fin r → Type*}
    (input : ∀ g,Y g→HeadInput)
    (hc : ∀ g h,h∈(tables g).choices ↔ ∃ y,input g y=h) (heads : List HeadInput) :
    heads∈enumerate (List.ofFn tables) ↔ ∃ y,tupleHeads input y=heads := by
  rw [mem_enumerate]
  constructor
  · intro hh
    have hlen : heads.length=r := by simpa using hh.length_eq.symm
    let atHead (g : Fin r) := heads.get (Fin.cast hlen.symm g)
    have hm (g : Fin r) : atHead g∈(tables g).choices := by
      have hp := hh.get (i:=g.val) (by simp) (by rw [hlen]; exact g.isLt)
      simpa [atHead,List.get_eq_getElem] using hp
    choose y hy using fun g=>(hc g (atHead g)).mp (hm g)
    refine ⟨y,?_⟩
    apply List.ext_getElem
    · simp [tupleHeads,hlen]
    · intro i hi hj
      have hir : i < r := by simpa [tupleHeads] using hi
      simpa [tupleHeads,atHead,List.get_eq_getElem] using hy ⟨i,hir⟩
  · rintro ⟨y,rfl⟩
    apply List.forall₂_of_length_eq_of_get
    · simp [tupleHeads]
    · intro i hi hj
      have hir : i < r := by simpa using hi
      have hm := (hc ⟨i,hir⟩ (input ⟨i,hir⟩ (y ⟨i,hir⟩))).mpr ⟨y ⟨i,hir⟩,rfl⟩
      simpa [tupleHeads,List.get_eq_getElem] using hm

theorem tuple_enumeration {r : ℕ} (tables : Fin r → HeadTable) {Y : Fin r → Type*}
    (input : ∀ g,Y g→HeadInput) (hi : ∀ g,Function.Injective (input g))
    (hc : ∀ g h,h∈(tables g).choices ↔ ∃ y,input g y=h)
    (hn : ∀ g,(tables g).choices.Nodup) :
    ∃ ys : List (∀ g,Y g),ys.Nodup ∧ (∀ y,y∈ys) ∧
      ys.map (tupleHeads input)=enumerate (List.ofFn tables) := by
  apply finite_reindex _ _ (tupleHeads_injective input hi)
  · apply enumerate_nodup
    intro table ht
    obtain ⟨g,rfl⟩ := List.mem_ofFn.mp ht
    exact hn g
  · exact tupleHeads_mem_iff tables input hc

theorem finalized_enumeration {r : ℕ} (n : ℕ) (tables : Fin r → HeadTable)
    {Y : Fin r → Type*} (input : ∀ g,Y g→HeadInput)
    (hi : ∀ g,Function.Injective (input g))
    (hc : ∀ g h,h∈(tables g).choices ↔ ∃ y,input g y=h)
    (hn : ∀ g,(tables g).choices.Nodup) :
    ∃ ys : List (∀ g,Y g),ys.Nodup ∧ (∀ y,y∈ys) ∧
      ys.map (fun y=>Representative.bucket n (tupleHeads input y))=
        ((enumerate (List.ofFn tables)).map (Representative.bucket n)).reverse := by
  obtain ⟨ys,hyn,hyc,he⟩ := tuple_enumeration tables input hi hc hn
  refine ⟨ys.reverse,List.nodup_reverse.mpr hyn,?_,?_⟩
  · intro y
    simpa using hyc y
  · rw [List.map_reverse,←he,List.map_map]
    rfl

end SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete

end

end OAI.Algorithms
