import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CompanionSequence
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.Sequence

/-! # Companion -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

/-! Native endpoints, terminal residual drop, and total-control concatenation of global companion phases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Resolution.Blowups.Global.CompanionSequence.Construction.SmoothGlobalCompanionSequence

def CompanionSequence.Construction.SmoothGlobalCompanionSequence.endpoint {m b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {M J : X.IdealSheafData}
    (T : CompanionSequence.Construction.SmoothGlobalCompanionSequence m b X f M J) : Scheme :=
  match T with
  | @terminal _ _ Y _ _ _ _ _ _ => Y
  | @blowup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tail => tail.endpoint

def CompanionSequence.Construction.SmoothGlobalCompanionSequence.toBase {m b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {M J : X.IdealSheafData}
    (T : CompanionSequence.Construction.SmoothGlobalCompanionSequence m b X f M J) : T.endpoint ⟶ X :=
  match T with
  | @terminal _ _ Y _ _ _ _ _ _ => 𝟙 Y
  | @blowup _ _ _ _ _ _ _ _ _ _ I hI _ _ _ _ tail => tail.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI

def CompanionSequence.Construction.SmoothGlobalCompanionSequence.exceptionalIdeal {m b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {M J : X.IdealSheafData}
    (T : CompanionSequence.Construction.SmoothGlobalCompanionSequence m b X f M J) : T.endpoint.IdealSheafData :=
  match T with
  | @terminal _ _ _ _ _ M _ _ _ => M
  | @blowup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tail => tail.exceptionalIdeal

def CompanionSequence.Construction.SmoothGlobalCompanionSequence.residualIdeal {m b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {M J : X.IdealSheafData}
    (T : CompanionSequence.Construction.SmoothGlobalCompanionSequence m b X f M J) : T.endpoint.IdealSheafData :=
  match T with
  | @terminal _ _ _ _ _ _ J _ _ => J
  | @blowup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tail => tail.residualIdeal

variable {m b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {M J : X.IdealSheafData}

instance CompanionSequence.Construction.SmoothGlobalCompanionSequence.toBase_isProper (T : CompanionSequence.Construction.SmoothGlobalCompanionSequence m b X f M J) : IsProper T.toBase := by
  induction T with
  | @terminal Y g hs M J hb hd => exact inferInstanceAs (IsProper (𝟙 Y))
  | blowup hb I hI hM hJ hs hbl tail ih =>
      let : IsProper tail.toBase := ih
      exact inferInstanceAs (IsProper (tail.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI))

instance CompanionSequence.Construction.SmoothGlobalCompanionSequence.endpoint_structure_smooth (T : CompanionSequence.Construction.SmoothGlobalCompanionSequence m b X f M J) : Smooth (T.toBase ≫ f) := by
  induction T with
  | @terminal Y g hs M J hb hd => simpa only [CompanionSequence.Construction.SmoothGlobalCompanionSequence.endpoint, CompanionSequence.Construction.SmoothGlobalCompanionSequence.toBase, Category.id_comp] using hs
  | blowup hb I hI hM hJ hs hbl tail ih => simpa only [CompanionSequence.Construction.SmoothGlobalCompanionSequence.endpoint, CompanionSequence.Construction.SmoothGlobalCompanionSequence.toBase, Category.assoc] using ih

theorem CompanionSequence.Construction.SmoothGlobalCompanionSequence.endpoint_integral (T : CompanionSequence.Construction.SmoothGlobalCompanionSequence m b X f M J) [IsIntegral X] :
    IsIntegral T.endpoint := by
  revert ‹IsIntegral X›
  induction T with
  | terminal => intro h; exact h
  | blowup hb I hI hM hJ hs hbl tail ih => intro _; exact ih

def CompanionSequence.Construction.SmoothGlobalCompanionSequence.endpointProjectivePresentation (T : CompanionSequence.Construction.SmoothGlobalCompanionSequence m b X f M J)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f) : Foundations.Scheme.SmoothProjective.ProjectivePresentation T.endpoint (T.toBase ≫ f) := by
  induction T with
  | terminal => simpa only [CompanionSequence.Construction.SmoothGlobalCompanionSequence.endpoint, CompanionSequence.Construction.SmoothGlobalCompanionSequence.toBase, Category.id_comp] using P
  | blowup hb I hI hM hJ hs hbl tail ih =>
      have Q := ih (GlobalBlowup.Projectivity.Construction.globalBlowupProjectivePresentation P I hI)
      simpa only [CompanionSequence.Construction.SmoothGlobalCompanionSequence.endpoint, CompanionSequence.Construction.SmoothGlobalCompanionSequence.toBase, Category.assoc] using Q

theorem CompanionSequence.Construction.SmoothGlobalCompanionSequence.terminal_residual_bound (T : CompanionSequence.Construction.SmoothGlobalCompanionSequence m b X f M J) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (T.toBase ≫ f) T.residualIdeal m = ⊤ := by
  induction T with
  | @terminal Y g hs M J hb hd =>
      change Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (𝟙 Y ≫ g) J m = ⊤
      rw [DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_structure_congr (𝟙 Y ≫ g) g (Category.id_comp g)]
      exact hb
  | @blowup Y hY hN g hg M J hb I hI hM hJ hs hbl tail ih =>
      let π := GlobalBlowup.Data.Construction.globalBlowupToBase I hI
      let : Smooth (π ≫ g) := hbl
      let : Smooth ((tail.toBase ≫ π) ≫ g) := by
        rw [Category.assoc]
        exact tail.endpoint_structure_smooth
      change Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf ((tail.toBase ≫ π) ≫ g) tail.residualIdeal m = ⊤
      rw [DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_structure_congr ((tail.toBase ≫ π) ≫ g)
        (tail.toBase ≫ (π ≫ g)) (Category.assoc _ _ _)]
      exact ih

theorem CompanionSequence.Construction.SmoothGlobalCompanionSequence.terminal_residual_drop (T : CompanionSequence.Construction.SmoothGlobalCompanionSequence m b X f M J) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (T.toBase ≫ f) (T.exceptionalIdeal * T.residualIdeal) (b - 1) ⊔
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (T.toBase ≫ f) T.residualIdeal (m - 1) = ⊤ := by
  induction T with
  | @terminal Y g hs M J hb hd =>
      change Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (𝟙 Y ≫ g) (M * J) (b - 1) ⊔
        Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (𝟙 Y ≫ g) J (m - 1) = ⊤
      rw [DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_structure_congr (𝟙 Y ≫ g) g (Category.id_comp g),
        DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_structure_congr (𝟙 Y ≫ g) g (Category.id_comp g)]
      exact hd
  | @blowup Y hY hN g hg M J hb I hI hM hJ hs hbl tail ih =>
      let π := GlobalBlowup.Data.Construction.globalBlowupToBase I hI
      let : Smooth (π ≫ g) := hbl
      let : Smooth ((tail.toBase ≫ π) ≫ g) := by
        rw [Category.assoc]
        exact tail.endpoint_structure_smooth
      change Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf ((tail.toBase ≫ π) ≫ g) (tail.exceptionalIdeal * tail.residualIdeal) (b - 1) ⊔
        Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf ((tail.toBase ≫ π) ≫ g) tail.residualIdeal (m - 1) = ⊤
      rw [DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_structure_congr ((tail.toBase ≫ π) ≫ g)
        (tail.toBase ≫ (π ≫ g)) (Category.assoc _ _ _),
        DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_structure_congr ((tail.toBase ≫ π) ≫ g)
          (tail.toBase ≫ (π ≫ g)) (Category.assoc _ _ _)]
      exact ih

def CompanionSequence.Construction.SmoothGlobalCompanionSequence.attachControl (T : CompanionSequence.Construction.SmoothGlobalCompanionSequence m b X f M J) (hb : 0 < b) (hmb : m ≤ b)
    (rest : MonomialSequence.Construction.SmoothFixedControlSequence b T.endpoint (T.toBase ≫ f) (T.exceptionalIdeal * T.residualIdeal)) :
    MonomialSequence.Construction.SmoothFixedControlSequence b X f (M * J) := by
  induction T with
  | @terminal Y g hs M J hbound hdrop =>
      change MonomialSequence.Construction.SmoothFixedControlSequence b Y (𝟙 Y ≫ g) (M * J) at rest
      simpa only [Category.id_comp] using rest
  | @blowup Y hY hN g hg M J hbound I hI hM hJ hs hbl tail ih =>
      have hp : M * J ≤ I ^ b := by
        intro U
        exact ResidualCoefficientTransform.Construction.product_center_permissible (I.ideal U) (M.ideal U) (J.ideal U) (b - m) m b (by omega) (hM U) (hJ U)
      apply MonomialSequence.Construction.SmoothFixedControlSequence.blowup I hI hb hp hs hbl
      rw [CompanionTransform.Construction.globalBlowup_companion_product_transform I M J hI m b hmb hM hJ]
      apply ih
      change MonomialSequence.Construction.SmoothFixedControlSequence b tail.endpoint ((tail.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI) ≫ g)
        (tail.exceptionalIdeal * tail.residualIdeal) at rest
      simpa only [Category.assoc] using rest

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
