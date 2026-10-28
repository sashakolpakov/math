import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MonomialSequence
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Projectivity
import OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective

/-! # Sequence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

/-! Actual proper birational morphisms and smooth projective endpoints of finite global control sequences. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Sequence.Construction.compatible_partialIso_comp {Z Y X : Scheme} (ψ : Z ⟶ Y) (π : Y ⟶ X)
    (e : Z.PartialIso Y) (he : e.source.ι ≫ ψ = e.iso.hom ≫ e.target.ι)
    (d : Y.PartialIso X) (hd : d.source.ι ≫ π = d.iso.hom ≫ d.target.ι) :
    (e.trans d).source.ι ≫ (ψ ≫ π) = (e.trans d).iso.hom ≫ (e.trans d).target.ι := by
  have he' : e.IsOver (ψ ≫ π) π := by
    change e.iso.hom ≫ e.target.ι ≫ π = e.source.ι ≫ ψ ≫ π
    simpa only [Category.assoc] using (congrArg (fun g => g ≫ π) he).symm
  have hd' : d.IsOver π (𝟙 X) := by
    simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using hd.symm
  have h := he'.trans hd'
  simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using Eq.symm h

open OAI.AlgebraicGeometry.Resolution.Blowups.Global.MonomialSequence.Construction.SmoothFixedControlSequence

def MonomialSequence.Construction.SmoothFixedControlSequence.endpoint {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (s : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) : Scheme :=
  match s with
  | @terminal _ Y _ _ _ _ => Y
  | @blowup _ _ _ _ _ _ _ _ _ _ _ _ tail => tail.endpoint

def MonomialSequence.Construction.SmoothFixedControlSequence.toBase {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (s : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) : s.endpoint ⟶ X :=
  match s with
  | @terminal _ Y _ _ _ _ => 𝟙 Y
  | @blowup _ _ _ _ _ _ I hI _ _ _ _ tail => tail.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI

def MonomialSequence.Construction.SmoothFixedControlSequence.terminalIdeal {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (s : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) : s.endpoint.IdealSheafData :=
  match s with
  | @terminal _ _ _ _ K _ => K
  | @blowup _ _ _ _ _ _ _ _ _ _ _ _ tail => tail.terminalIdeal

variable {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}

instance MonomialSequence.Construction.SmoothFixedControlSequence.toBase_isProper (s : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) : IsProper s.toBase := by
  induction s with
  | @terminal Y _ _ _ _ => exact inferInstanceAs (IsProper (𝟙 Y))
  | blowup I hI hb hperm hsmooth hblowup tail ih =>
      let : IsProper tail.toBase := ih
      exact inferInstanceAs (IsProper (tail.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI))

instance MonomialSequence.Construction.SmoothFixedControlSequence.endpoint_structure_smooth (s : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) : Smooth (s.toBase ≫ f) := by
  induction s with
  | @terminal _ g hs _ _ => simpa only [MonomialSequence.Construction.SmoothFixedControlSequence.endpoint, MonomialSequence.Construction.SmoothFixedControlSequence.toBase, Category.id_comp] using hs
  | blowup I hI hb hperm hsmooth hblowup tail ih =>
      simpa only [MonomialSequence.Construction.SmoothFixedControlSequence.endpoint, MonomialSequence.Construction.SmoothFixedControlSequence.toBase, Category.assoc] using ih

theorem MonomialSequence.Construction.SmoothFixedControlSequence.endpoint_integral (s : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) [IsIntegral X] :
    IsIntegral s.endpoint := by
  revert ‹IsIntegral X›
  induction s with
  | @terminal Y _ _ _ _ => intro hY; exact hY
  | blowup I hI hb hperm hsmooth hblowup tail ih =>
      intro _
      exact ih

theorem MonomialSequence.Construction.SmoothFixedControlSequence.toBase_partialIso (s : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) :
    ∃ e : s.endpoint.PartialIso X, e.source.ι ≫ s.toBase = e.iso.hom ≫ e.target.ι := by
  induction s with
  | @terminal Y g hs K ht =>
      refine ⟨Scheme.PartialIso.refl Y, ?_⟩
      change (⊤ : Y.Opens).ι ≫ 𝟙 Y = 𝟙 (⊤ : Y.Opens).toScheme ≫ (⊤ : Y.Opens).ι
      simp only [Category.comp_id, Category.id_comp]
  | blowup I hI hb hperm hsmooth hblowup tail ih =>
      obtain ⟨e, he⟩ := ih
      obtain ⟨d, hd⟩ := GlobalBlowup.Data.Construction.globalBlowup_partialIso I hI
      exact ⟨e.trans d, Sequence.Construction.compatible_partialIso_comp tail.toBase (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) e he d hd⟩

def MonomialSequence.Construction.SmoothFixedControlSequence.endpointProjectivePresentation (s : MonomialSequence.Construction.SmoothFixedControlSequence b X f J)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f) : Foundations.Scheme.SmoothProjective.ProjectivePresentation s.endpoint (s.toBase ≫ f) := by
  induction s with
  | terminal => simpa only [MonomialSequence.Construction.SmoothFixedControlSequence.endpoint, MonomialSequence.Construction.SmoothFixedControlSequence.toBase, Category.id_comp] using P
  | blowup I hI hb hperm hsmooth hblowup tail ih =>
      have Q := ih (GlobalBlowup.Projectivity.Construction.globalBlowupProjectivePresentation P I hI)
      simpa only [MonomialSequence.Construction.SmoothFixedControlSequence.endpoint, MonomialSequence.Construction.SmoothFixedControlSequence.toBase, Category.assoc] using Q

theorem MonomialSequence.Construction.SmoothFixedControlSequence.terminal_differential_ideal (s : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (s.toBase ≫ f) s.terminalIdeal (b - 1) = ⊤ := by
  induction s with
  | @terminal Y g _ K ht =>
      change Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (𝟙 Y ≫ g) K (b - 1) = ⊤
      exact (DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_structure_congr (𝟙 Y ≫ g) g
        (Category.id_comp g) K (b - 1)).trans ht
  | @blowup Y _ _ g K I hI hb hperm hsmooth hblowup tail ih =>
      let : Smooth ((tail.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI) ≫ g) := by
        rw [Category.assoc]
        exact MonomialSequence.Construction.SmoothFixedControlSequence.endpoint_structure_smooth tail
      change Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf ((tail.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI) ≫ g)
        tail.terminalIdeal (b - 1) = ⊤
      exact (DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_structure_congr
        ((tail.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI) ≫ g)
        (tail.toBase ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ g)) (Category.assoc _ _ _)
        tail.terminalIdeal (b - 1)).trans ih

def MonomialSequence.Construction.SmoothFixedControlSequence.endpointVariety (s : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) [IsIntegral X]
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f) : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety :=
  ⟨{ carrier := s.endpoint
     structureMap := s.toBase ≫ f
     projective := s.endpointProjectivePresentation P
     smooth := inferInstance }, s.endpoint_integral⟩

theorem MonomialSequence.Construction.SmoothFixedControlSequence.terminalIdeal_eq_top_control_one (s : MonomialSequence.Construction.SmoothFixedControlSequence 1 X f J) :
    s.terminalIdeal = ⊤ := by
  have h := s.terminal_differential_ideal
  change Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (s.toBase ≫ f) s.terminalIdeal 0 = ⊤ at h
  rwa [Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf_zero] at h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
