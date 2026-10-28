import OAI.AlgebraicGeometry.Resolution.Blowups.Global.Sequence
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SequenceStepCountTransport

/-! # Control Prefix -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ControlPrefix.Construction

noncomputable section

/-! Finite actual permissible smooth blowup prefixes with an explicit endpoint, available before the order locus is resolved. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

inductive SmoothControlPrefix (b : ℕ) :
    (X : Scheme) → (X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) → X.IdealSheafData →
      (Y : Scheme) → (Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) → Y.IdealSheafData → Type 1
  | stop {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData} :
      SmoothControlPrefix b X f J X f J
  | blowup {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
      {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
      (I : X.IdealSheafData) (hI : I ≠ ⊥) (hb : 0 < b) (hp : J ≤ I ^ b)
      (hs : Smooth (I.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f))
      {Y : Scheme} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData}
      (tail : SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) Y g K) : SmoothControlPrefix b X f J Y g K

namespace SmoothControlPrefix

variable {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData}

def toBase (P : Construction.SmoothControlPrefix b X f J Y g K) : Y ⟶ X := by
  induction P with
  | stop => exact 𝟙 _
  | blowup I hI _ _ _ _ _ ih => exact ih ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI

theorem over (P : Construction.SmoothControlPrefix b X f J Y g K) : P.toBase ≫ f = g := by
  induction P with
  | stop => exact Category.id_comp _
  | blowup I hI hb hp hs hbl tail ih =>
      change (tail.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI) ≫ _ = _
      rw [Category.assoc]
      exact ih

def stepCount (P : Construction.SmoothControlPrefix b X f J Y g K) : ℕ := by
  induction P with
  | stop => exact 0
  | blowup _ _ _ _ _ _ _ ih => exact ih + 1

def followsCenters (P : Construction.SmoothControlPrefix b X f J Y g K) : List X.IdealSheafData → Prop := by
  induction P with
  | stop => exact fun centers => centers = []
  | blowup I hI _ _ _ _ _ ih =>
      exact fun centers => ∃ rest, centers = I :: rest ∧
        ih (rest.map (fun L => L.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)))

def attach (P : Construction.SmoothControlPrefix b X f J Y g K)
    (S : Global.MonomialSequence.Construction.SmoothFixedControlSequence b Y g K) : Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f J := by
  induction P with
  | stop => exact S
  | blowup I hI hb hp hs hbl tail ih => exact .blowup I hI hb hp hs hbl (ih S)

theorem attach_stepCount (P : Construction.SmoothControlPrefix b X f J Y g K)
    (S : Global.MonomialSequence.Construction.SmoothFixedControlSequence b Y g K) : (P.attach S).stepCount = P.stepCount + S.stepCount := by
  induction P with
  | stop => exact (Nat.zero_add _).symm
  | blowup I hI hb hp hs hbl tail ih =>
      change (tail.attach S).stepCount + 1 = (tail.stepCount + 1) + S.stepCount
      rw [ih]
      omega

theorem endpoint_smooth (P : Construction.SmoothControlPrefix b X f J Y g K) : Smooth g := by
  induction P with
  | stop => infer_instance
  | blowup _ _ _ _ _ _ _ ih => exact ih

instance toBase_isProper (P : Construction.SmoothControlPrefix b X f J Y g K) : IsProper P.toBase := by
  induction P with
  | stop => exact inferInstanceAs (IsProper (𝟙 _))
  | blowup I hI hb hp hs hbl tail ih =>
      let : IsProper tail.toBase := ih
      exact inferInstanceAs (IsProper (tail.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI))

theorem endpoint_integral (P : Construction.SmoothControlPrefix b X f J Y g K) [IsIntegral X] : IsIntegral Y := by
  revert ‹IsIntegral X›
  induction P with
  | stop => intro h; exact h
  | blowup _ _ _ _ _ _ _ ih =>
      intro _
      exact ih

theorem endpoint_ideal_ne_bot (P : Construction.SmoothControlPrefix b X f J Y g K) (hJ : J ≠ ⊥) : K ≠ ⊥ := by
  induction P with
  | stop => exact hJ
  | @blowup X hX hN f J I hI hb hp hs hbl Y g K tail ih =>
      exact ih (GlobalBlowup.Nonzero.Construction.globalBlowupControlledIdeal_ne_bot I J hI b hJ)

end SmoothControlPrefix

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ControlPrefix.Construction
