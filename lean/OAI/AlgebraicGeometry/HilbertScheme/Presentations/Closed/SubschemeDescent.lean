import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.CoverGluing

/-! # Subscheme Descent -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.SubschemeDescent

noncomputable section

/-! Actual descent of compatible closed subschemes along an open cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X : Scheme.{u}} (U : X.OpenCover.{u}) (Z : U.I₀ → Scheme.{u})
variable (c : ∀ i, Z i ⟶ U.X i) [∀ i, IsClosedImmersion (c i)]
variable (hc : ∀ i j, (c i).ker.comap (pullback.fst (U.f i) (U.f j)) =
  (c j).ker.comap (pullback.snd (U.f i) (U.f j)))

instance closedCoverParameter_isClosedImmersion :
    IsClosedImmersion (CoverGluing.closedCoverParameter U.X Z U.f c hc) := by
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) U).mpr
  intro i
  let h := (CoverGluing.closedCoverChart_isPullback U.X Z U.f c hc i).flip
  have H : IsClosedImmersion (h.isoPullback.inv ≫ c i) := inferInstance
  rwa [h.isoPullback_inv_snd] at H

def descendedClosedIdeal : X.IdealSheafData := (CoverGluing.closedCoverParameter U.X Z U.f c hc).ker

theorem descendedClosedIdeal_comap (i : U.I₀) :
    (descendedClosedIdeal U Z c hc).comap (U.f i) = (c i).ker := by
  let h := CoverGluing.closedCoverChart_isPullback U.X Z U.f c hc i
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  rfl

include hc in
theorem closed_subscheme_descent :
    ∃ I : X.IdealSheafData, ∀ i, I.comap (U.f i) = (c i).ker :=
  ⟨descendedClosedIdeal U Z c hc, descendedClosedIdeal_comap U Z c hc⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.SubschemeDescent
