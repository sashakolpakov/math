import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutInterface

namespace OAI.Algorithms

/-! Runtime row order and basis choices need not match `Fintype.equivFin`.
Any explicitly supplied integer row family spanning the old one over the
rationals retains exact locality with the same polynomial rows and heads. -/
namespace SubexponentialSAT.SqrtLog.Layout

open LayoutExactBuckets

variable {V I F G O : Type*} [Fintype V] [DecidableEq V]
  [Fintype G] [DecidableEq G] [CommRing O]
variable {owner : I → V} {factor : I → F} {Q R : ℕ}

namespace Data

def replaceConstraints (L : Data (O := O) (G := G) owner factor Q R)
    (count : Fin Q → G → ℕ)
    (A : (t : Fin Q) → (g : G) → Fin (count t g) → L.Head t g → ℤ)
    (hspan : ∀ t g, RationalRowSpan (L.constraints t g) (A t g)) :
    Data (O := O) (G := G) owner factor Q R where
  node := L.node
  units := L.units
  head := L.head
  color := L.color
  row := L.row
  row_origin := L.row_origin
  row_degree := L.row_degree
  rowCount := count
  constraints := A
  locality := fun t i g hg => killsIntegerKernel_of_rational_span
    (L.constraints t g) (A t g) (hspan t g) _ (L.locality t i g hg)

end Data

end SubexponentialSAT.SqrtLog.Layout

namespace SubexponentialSAT.SqrtLog.LayoutExactBuckets

variable {V J K : Type*} [Fintype V]

/-- Reordering or redundantly enumerating all rows preserves the exact
integer signature partition. This is independent of a chosen row basis. -/
theorem signature_reindex_eq_iff (A : J → V → ℤ) (e : K → J)
    (he : Function.Surjective e) (x y : V → ℤ) :
    signature (fun k => A (e k)) x = signature (fun k => A (e k)) y ↔
      signature A x = signature A y := by
  constructor
  · intro h
    funext j
    obtain ⟨k,rfl⟩ := he j
    exact congrFun h k
  · intro h
    funext k
    exact congrFun h (e k)

end SubexponentialSAT.SqrtLog.LayoutExactBuckets

end OAI.Algorithms
