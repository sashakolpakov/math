import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Finite Closed Fibers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FiniteClosedFibers

noncomputable section

/-! A proper map to a Jacobson scheme is finite when its fibers over closed points have finite support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem proper_isFinite_of_finite_closedFibers (f : X ⟶ Y) [IsProper f] [JacobsonSpace Y]
    (h : ∀ y : Y, IsClosed ({y} : Set Y) → (f ⁻¹' {y}).Finite) : IsFinite f := by
  let I := {U : Y.Opens // IsFinite (f ∣_ U)}
  let V : Y.Opens := ⨆ U : I, U.val
  have hclosed (y : Y) (hy : IsClosed ({y} : Set Y)) : y ∈ V := by
    obtain ⟨U, hyU, hU⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f y (h y hy)
    exact (le_iSup (fun U : I => U.val) ⟨U, hU⟩) hyU
  have hV : V = ⊤ := by
    apply top_unique
    intro y _
    by_contra hy
    obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints
      (show ((V : Set Y)ᶜ).Nonempty from ⟨y, hy⟩) V.isOpen.isClosed_compl.isLocallyClosed
    exact hz (hclosed z hzc)
  have hQ : f.quasiFiniteLocus = ⊤ := by
    apply top_unique
    intro x _
    have hm : f x ∈ V := hV.symm ▸ (show f x ∈ (⊤ : Y.Opens) from trivial)
    change f x ∈ (⨆ U : I, U.val) at hm
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hm
    let : IsFinite (f ∣_ U.val) := U.property
    let xU : (f ⁻¹ᵁ U.val).toScheme := ⟨x, hU⟩
    have hxU : (f ∣_ U.val).QuasiFiniteAt xU := (f ∣_ U.val).quasiFiniteAt xU
    have hc : ((f ∣_ U.val) ≫ U.val.ι).QuasiFiniteAt xU :=
      Scheme.Hom.quasiFiniteAt_comp_iff.mpr hxU
    have hc' : ((f ⁻¹ᵁ U.val).ι ≫ f).QuasiFiniteAt xU := (morphismRestrict_ι f U.val) ▸ hc
    exact Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion.mp hc'
  have : LocallyQuasiFinite f := f.quasiFiniteLocus_eq_top_iff.mp hQ
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FiniteClosedFibers
