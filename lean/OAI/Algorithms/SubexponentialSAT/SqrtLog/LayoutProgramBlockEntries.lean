import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBlocks
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking

namespace OAI.Algorithms

/-! Exact dispatch formulas for the integer block matrix. These identify the
results of metadata equality tests and scalar-array reads with the raw layout
constraints, before the owner-fiber sum is performed. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.Subexp.ConstructivePacking LayoutPullback

variable {U I G O : Type*}
variable [Fintype U] [DecidableEq U] [Fintype I] [DecidableEq I]
variable [Fintype G] [DecidableEq G] [CommRing O]
variable {Q R : ℕ}

omit [Fintype I] [Fintype G] in
theorem embedHead_injective
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : PackingData I U) (t : Fin Q) (g : G) (j : Fin P.blockCount) :
    Function.Injective (LayoutBlocks.embedHead C P.completeBlocks t g j) := by
  intro x y h
  apply Subtype.ext
  have hh := P.completeBlocks.embed.injective (congrArg Subtype.val h)
  exact congrArg Prod.snd hh

omit [Fintype I] [Fintype G] in
theorem blockConstraint_covered
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : PackingData I U) (t : Fin Q) (g : G)
    (j k : Fin P.blockCount) (a : Fin (C.rowCount t g))
    (u : {u : U // C.head t u = g}) :
    LayoutBlocks.constraints C P.completeBlocks t g (.inl (j,a))
      (LayoutBlocks.embedHead C P.completeBlocks t g k u) =
      if j = k then C.constraints t g a u else 0 := by
  by_cases hj : j = k
  · subst k
    simp only [LayoutBlocks.constraints ]
    exact row_apply_injective _ (embedHead_injective C P t g j) _ u
  · have hout : LayoutBlocks.embedHead C P.completeBlocks t g k u ∉
        Set.range (LayoutBlocks.embedHead C P.completeBlocks t g j) := by
      rintro ⟨y,hy⟩
      have hh := P.completeBlocks.embed.injective (congrArg Subtype.val hy)
      exact hj (congrArg Prod.fst hh)
    simp only [LayoutBlocks.constraints, ite_eq_right hj]
    exact row_eq_zero _ _ _ hout

omit [Fintype G] in
omit [Fintype I] in
theorem blockConstraint_uncovered
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : PackingData I U) (t : Fin Q) (g : G)
    (j : Fin P.blockCount) (a : Fin (C.rowCount t g))
    (v : {i : I // LayoutBlocks.copyHead C P.label t i = g})
    (hv : v.val ∉ Set.range P.completeBlocks.embed) :
    LayoutBlocks.constraints C P.completeBlocks t g (.inl (j,a)) v = 0 := by
  have hout : v ∉ Set.range (LayoutBlocks.embedHead C P.completeBlocks t g j) := by
    rintro ⟨u,hu⟩
    exact hv ⟨(j,u.val), congrArg Subtype.val hu⟩
  exact row_eq_zero _ _ _ hout

omit [Fintype I] [Fintype G] in
theorem singletonConstraint
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : PackingData I U) (t : Fin Q) (g : G)
    (v : {v : {i : I // LayoutBlocks.copyHead C P.label t i = g} //
      v.val ∉ Set.range P.completeBlocks.embed})
    (w : {i : I // LayoutBlocks.copyHead C P.label t i = g}) :
    LayoutBlocks.constraints C P.completeBlocks t g (.inr v) w =
      if w.val = v.val.val then 1 else 0 := by
  simp [LayoutBlocks.constraints, Pi.single_apply, Subtype.ext_iff ]

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
