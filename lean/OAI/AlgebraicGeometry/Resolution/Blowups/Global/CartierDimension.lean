import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalRegular
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ClosedCarrierBoundaryAtlas
import OAI.AlgebraicGeometry.Resolution.Blowups.Open.CoverDimension
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-! # Cartier Dimension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.CartierDimension.Construction

noncomputable section

/-! A nonzero locally principal closed carrier drops the ambient dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem locallyPrincipal_subscheme_dimension_le
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (H : X.IdealSheafData) (hH : H ≠ ⊥) (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H)
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d + 1 : ℕ)) :
    topologicalKrullDim H.subscheme ≤ d := by
  classical
  choose U hx r hregular hHlocal using Locally.PrincipalRegular.Construction.locallyPrincipal_regular_generators H hH hlocal
  have hcover : ⨆ x, (U x).1 = ⊤ := by
    apply top_le_iff.mp
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  let C := ClosedCarrierBoundaryAtlas.Construction.subschemeChosenAffineCover H U hcover
  let : ∀ i, IsOpenImmersion (C.f i) := fun i => C.openCover.map_prop i
  apply Open.CoverDimension.Construction.scheme_dimension_le_of_open_affine_cover C.X C.f
    (fun x => ⟨C.idx x, C.covers x⟩) d
  intro x
  change ringKrullDim (Γ(X, U x) ⧸ H.ideal (U x)) ≤ d
  rw [hHlocal x]
  let : IsOpenImmersion (U x).2.fromSpec := (U x).2.isOpenImmersion_fromSpec
  have h := (ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (hregular x).mem_nonZeroDivisors).trans
    ((Open.CoverDimension.Construction.ringKrullDim_le_of_affine_open_map Γ(X, U x) (U x).2.fromSpec).trans hd)
  rw [Nat.cast_add, Nat.cast_one] at h
  exact ENat.WithBot.add_le_add_one_right_iff.mp h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.CartierDimension.Construction
