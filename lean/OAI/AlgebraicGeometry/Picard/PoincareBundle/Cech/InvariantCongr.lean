import OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointCechInvariant

/-! # Invariant Congr -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.InvariantCongr

noncomputable section

/-!
# Equal geometric comparison data retain the invariant and its canonical map
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointCechInvariant

variable {C D E : Type*} [Category C] [Category D] [Category E]
  {L : C ⥤ D} {R : D ⥤ C} {P Q : D ⥤ E} {U V : E ⥤ D}
  (a : L ⊣ R) (b : P ⊣ U) (c : Q ⊣ V) [HasEqualizers C]
  {e e' : U ⋙ R ≅ V ⋙ R} {M : D} {σ σ' : P.obj M ⟶ Q.obj M}

/-- The equality-transport isomorphism between the actual invariant objects. -/
def invariantIso (he : e = e') (hσ : σ = σ') : AdjointCechInvariant.invariants b c e σ ≅ AdjointCechInvariant.invariants b c e' σ' :=
  eqToIso (congrArg₂ (fun d t => AdjointCechInvariant.invariants b c d t) he hσ)

theorem comparison_fac (he : e = e') (hσ : σ = σ') :
    L.map (invariantIso b c he hσ).hom ≫ AdjointCechInvariant.comparison a b c e' σ' = AdjointCechInvariant.comparison a b c e σ := by
  subst e'
  subst σ'
  change L.map (𝟙 _) ≫ AdjointCechInvariant.comparison a b c e σ = _
  rw [L.map_id]
  exact Category.id_comp _

/-- Effectivity concerns the actual canonical comparison morphism. -/
def Effective (e : U ⋙ R ≅ V ⋙ R) (σ : P.obj M ⟶ Q.obj M) : Prop :=
  IsIso (AdjointCechInvariant.comparison a b c e σ)

theorem effective_congr (he : e = e') (hσ : σ = σ') :
    Effective a b c e σ ↔ Effective a b c e' σ' := by
  subst e'
  subst σ'
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.InvariantCongr
