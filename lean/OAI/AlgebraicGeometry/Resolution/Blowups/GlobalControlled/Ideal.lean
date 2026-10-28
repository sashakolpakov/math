import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.ColonRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Iteration

/-! # Ideal -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Ideal.Construction

noncomputable section

/-! The global controlled ideal on the actual blowup scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]

/-- Divide the actual total transform by the prescribed power of the
pulled-back center ideal. On a blowup this is the global controlled ideal. -/
def controlledIdealSheaf (I J : X.IdealSheafData) (b : ℕ) (π : Y ⟶ X) : Y.IdealSheafData :=
  NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon (J.comap π) ((I.comap π) ^ b)

/-- Its affine components are the actual ideal quotients of the pulled-back
ideals, with the original control exponent. -/
theorem controlledIdealSheaf_ideal (I J : X.IdealSheafData) (b : ℕ) (π : Y ⟶ X)
    (U : Y.affineOpens) :
    (controlledIdealSheaf I J b π).ideal U =
      ((J.comap π).ideal U).colon ((((I.comap π).ideal U) ^ b : Ideal Γ(Y, U)) : Set Γ(Y, U)) := rfl

theorem totalIdeal_le_controlledIdealSheaf (I J : X.IdealSheafData) (b : ℕ) (π : Y ⟶ X) :
    J.comap π ≤ controlledIdealSheaf I J b π := NoetherianIdealSheafColon.Construction.le_noetherianIdealSheafColon _ _

theorem controlledIdealSheaf_ne_bot (I J : X.IdealSheafData) (b : ℕ) (π : Y ⟶ X)
    (hJ : J.comap π ≠ ⊥) : controlledIdealSheaf I J b π ≠ ⊥ :=
  NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon_ne_bot _ _ hJ

variable {Z : Scheme.{u}} [IsLocallyNoetherian Z]

/-- The global controlled ideal restricts to the same construction on
every actual open chart of the transformed ambient scheme. -/
theorem controlledIdealSheaf_comap_open (I J : X.IdealSheafData) (b : ℕ) (π : Y ⟶ X)
    (g : Z ⟶ Y) [IsOpenImmersion g] :
    (controlledIdealSheaf I J b π).comap g = controlledIdealSheaf I J b (g ≫ π) := by
  unfold controlledIdealSheaf
  rw [IdealSheaf.ColonRestriction.Construction.noetherianIdealSheafColon_comap_open, IdealSheaf.ColonRestriction.Construction.idealSheaf_comap_pow_open,
    ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]

omit [IsLocallyNoetherian Z] in
/-- An isomorphic ambient blowup preserves nonzeroness of the controlled
ideal, so the next curve step still receives a nonzero global ideal. -/
theorem controlledIdealSheaf_ne_bot_of_isIso (I J : X.IdealSheafData) (b : ℕ) (π : Y ⟶ X)
    [IsIso π] (hJ : J ≠ ⊥) : controlledIdealSheaf I J b π ≠ ⊥ := by
  apply controlledIdealSheaf_ne_bot
  intro h
  have he := congrArg (fun L : Y.IdealSheafData => L.comap (inv π)) h
  rw [← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id,
    Scheme.IdealSheafData.comap_id, Scheme.IdealSheafData.comap_bot] at he
  exact hJ he

variable [IsIntegral X] [IsLocallyNoetherian X]

omit [IsLocallyNoetherian Y] [IsLocallyNoetherian Z] in
/-- The controlled ideal is a native ideal sheaf on the already constructed
global blowup, so it can be used as the ideal in a subsequent step. -/
def globalBlowupControlledIdeal (I J : X.IdealSheafData) (hI : I ≠ ⊥) (b : ℕ) :
    (GlobalBlowup.Data.Construction.globalBlowup I hI).IdealSheafData := controlledIdealSheaf I J b (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Ideal.Construction
