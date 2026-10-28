import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Morphism Compatible Affine Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.MorphismCompatibleAffineCover

noncomputable section

/-! Two original affine covers and a scheme morphism construct an
actual affine cover of the source refining both its original cover
and the inverse image of the target cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : X.AffineOpenCover) (V : Y.AffineOpenCover)

structure MorphismAffineRefinementIndex where
  source : U.I₀
  target : V.I₀
  chart : X.affineOpens
  source_le : chart.1 ≤ (U.f source).opensRange
  target_le : chart.1 ≤ f ⁻¹ᵁ (V.f target).opensRange

theorem morphismAffineRefinement_covers :
    iSup (fun i : MorphismAffineRefinementIndex f U V => i.chart.1) = ⊤ := by
  apply top_unique
  intro x _
  let i := U.idx x
  let j := V.idx (f x)
  have hx : x ∈ (U.f i).opensRange ⊓ f ⁻¹ᵁ (V.f j).opensRange := ⟨U.covers x, V.covers (f x)⟩
  obtain ⟨W, hW, hxW, hsub⟩ := exists_isAffineOpen_mem_and_subset hx
  apply Opens.mem_iSup.mpr
  refine ⟨⟨i, j, ⟨W, hW⟩, ?_, ?_⟩, hxW⟩
  · exact fun _ h => (hsub h).1
  · exact fun _ h => (hsub h).2

def morphismCompatibleAffineCover : X.AffineOpenCover :=
  Scheme.AffineOpenCover.ofIsOpenCover (fun i : MorphismAffineRefinementIndex f U V => i.chart.1)
    (morphismAffineRefinement_covers f U V) (fun i => i.chart.2)

instance morphismCompatibleAffineCover_open (i : MorphismAffineRefinementIndex f U V) :
    IsOpenImmersion ((morphismCompatibleAffineCover f U V).f i) :=
  IsAffineOpen.isOpenImmersion_fromSpec i.chart.2

theorem morphismCompatibleAffineCover_range (i : MorphismAffineRefinementIndex f U V) :
    ((morphismCompatibleAffineCover f U V).f i).opensRange = i.chart.1 :=
  i.chart.2.opensRange_fromSpec

theorem morphismCompatibleAffineCover_source (i : MorphismAffineRefinementIndex f U V) :
    ((morphismCompatibleAffineCover f U V).f i).opensRange ≤ (U.f i.source).opensRange := by
  rw [morphismCompatibleAffineCover_range]
  exact i.source_le

theorem morphismCompatibleAffineCover_target (i : MorphismAffineRefinementIndex f U V) :
    ((morphismCompatibleAffineCover f U V).f i).opensRange ≤ f ⁻¹ᵁ (V.f i.target).opensRange := by
  rw [morphismCompatibleAffineCover_range]
  exact i.target_le

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.MorphismCompatibleAffineCover
