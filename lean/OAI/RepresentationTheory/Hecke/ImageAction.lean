import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Image Action -/

namespace OAI.RepresentationTheory.Hecke.ImageAction.SphericalIntrinsic

noncomputable section

/-! Restrict an actual linear action to an invariant image. The algebra
laws follow from the intertwining source action and image surjectivity. -/

variable {k H S V : Type*} [Field k] [Ring H] [Algebra k H]
  [AddCommGroup S] [Module k S] [AddCommGroup V] [Module k V]
  (A : H →ₐ[k] Module.End k S) (T : S →ₗ[k] V)
  (B : H →ₗ[k] Module.End k V)
  (hc : ∀ h s, T (A h s) = B h (T s))

def imageOperator (h : H) : Module.End k T.range :=
  ((B h).comp T.range.subtype).codRestrict T.range (by
    rintro ⟨y, s, rfl⟩
    exact ⟨A h s, hc h s⟩)

theorem imageOperator_apply (h : H) (y : T.range) :
    (imageOperator A T B hc h y).val = B h y.val := rfl

theorem imageOperator_intertwines (h : H) (s : S) :
    T.rangeRestrict (A h s) = imageOperator A T B hc h (T.rangeRestrict s) := by
  exact Subtype.ext (hc h s)

def imageAction : H →ₐ[k] Module.End k T.range where
  toFun := imageOperator A T B hc
  map_zero' := by ext x; exact LinearMap.congr_fun B.map_zero x.val
  map_add' h l := by
    ext x
    exact LinearMap.congr_fun (B.map_add h l) x.val
  map_one' := by
    ext x
    obtain ⟨s, hs⟩ := x.property
    change B 1 x.val = x.val
    rw [← hs, ← hc, map_one]
    rfl
  map_mul' h l := by
    ext x
    obtain ⟨s, hs⟩ := x.property
    change B (h * l) x.val = B h (B l x.val)
    rw [← hs, ← hc, ← hc, ← hc, map_mul]
    rfl
  commutes' a := by
    ext x
    obtain ⟨s, hs⟩ := x.property
    change B (algebraMap k H a) x.val = a • x.val
    rw [← hs, ← hc, A.commutes]
    exact T.map_smul a s

theorem imageAction_intertwines (h : H) (s : S) :
    T.rangeRestrict (A h s) = imageAction A T B hc h (T.rangeRestrict s) :=
  imageOperator_intertwines A T B hc h s

end

end OAI.RepresentationTheory.Hecke.ImageAction.SphericalIntrinsic
