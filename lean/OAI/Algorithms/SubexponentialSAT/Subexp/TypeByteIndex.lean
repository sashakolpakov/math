import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.TypeEnumeration
import OAI.Algorithms.SubexponentialSAT.Subexp.SeedIndexFormulas

namespace OAI.Algorithms

/-!
# Actual byte-list indices for side and joint coordinates

The physical metadata lookup uses `idxOf` on encoded types. These
equivalences use that same list order, with dimensions stated as byte-list
lengths, so no reordering or equality of arbitrary enumerations is needed.
-/

namespace SubexponentialSAT.Subexp.TypeByteIndex

open MulticolorTypes TypeEnumeration

variable {r Q Δ : ℕ} (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r)

theorem side_length :
    (sideBytes r Q Δ t.val g.val).length = (sideList (Δ := Δ) hr hQ t g).length := by
  rw [← sideList_bytes hr hQ t g, List.length_map]

theorem joint_length (i : Fin Δ) :
    (jointBytes r Q Δ t.val g.val i.val).length = (jointList hr hQ t g i).length := by
  rw [← jointList_bytes hr hQ t g i, List.length_map]

noncomputable def sideByteEquiv :
    Fin (sideBytes r Q Δ t.val g.val).length ≃ Side (Δ := Δ) t g :=
  (finCongr (side_length hr hQ t g)).trans (sideEquiv hr hQ t g)

noncomputable def jointByteEquiv (i : Fin Δ) :
    Fin (jointBytes r Q Δ t.val g.val i.val).length ≃ Joint t g i :=
  (finCongr (joint_length hr hQ t g i)).trans (jointEquiv hr hQ t g i)

theorem sideByteEquiv_symm_val (u : Side (Δ := Δ) t g) :
    ((sideByteEquiv hr hQ t g).symm u).val =
      (sideBytes r Q Δ t.val g.val).idxOf (CollisionProgram.encodeType u.val) := by
  have hval : ((sideByteEquiv hr hQ t g).symm u).val =
      (sideList hr hQ t g).idxOf u := by
    simp [sideByteEquiv, sideEquiv, List.Nodup.getEquivOfForallMemList]
    simp only [List.idxOf, beq_eq_decide]
  rw [hval]
  rw [← sideList_bytes hr hQ t g]
  symm
  have h := SeedIndexFormulas.idxOf_map_injective
    (fun v : Side (Δ := Δ) t g => CollisionProgram.encodeType v.val)
    (by intro a b h; exact Subtype.ext (CollisionProgram.encodeType_injective h))
    (sideList hr hQ t g) u
  simpa only [List.idxOf, beq_eq_decide] using h

theorem jointByteEquiv_symm_val (i : Fin Δ) (u : Joint t g i) :
    ((jointByteEquiv hr hQ t g i).symm u).val =
      (jointBytes r Q Δ t.val g.val i.val).idxOf (CollisionProgram.encodeType u.val) := by
  have hval : ((jointByteEquiv hr hQ t g i).symm u).val =
      (jointList hr hQ t g i).idxOf u := by
    simp [jointByteEquiv, jointEquiv, List.Nodup.getEquivOfForallMemList]
    simp only [List.idxOf, beq_eq_decide]
  rw [hval]
  rw [← jointList_bytes hr hQ t g i]
  symm
  have h := SeedIndexFormulas.idxOf_map_injective
    (fun v : Joint t g i => CollisionProgram.encodeType v.val)
    (by intro a b h; exact Subtype.ext (CollisionProgram.encodeType_injective h))
    (jointList hr hQ t g i) u
  simpa only [List.idxOf, beq_eq_decide] using h

end SubexponentialSAT.Subexp.TypeByteIndex

end OAI.Algorithms
