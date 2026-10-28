import OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.CechInvariant
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.SquareNormalization
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.SquareGluing

/-! # Gluing Normalization -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.GluingNormalization

noncomputable section

/-!
# Open restriction and ordinary geometric gluing use the same comparison
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.AlgebraicGeometry

section

/-- Changing the endpoint and overlap presentations retains the gluing square. -/
theorem iso_transition_square {C : Type*} [Category C]
    {S₁ S₂ T₁ T₂ U₁ U₂ V₁ V₂ : C}
    (a₁ : S₁ ≅ T₁) (a₂ : S₂ ≅ T₂) (b₁ : T₁ ≅ U₁) (b₂ : T₂ ≅ U₂)
    (c₁ : V₁ ≅ U₁) (c₂ : V₂ ≅ U₂) (β : S₁ ≅ V₁) (γ : S₂ ≅ V₂)
    (s : V₁ ⟶ V₂) (t : U₁ ⟶ U₂)
    (hβ : β = a₁ ≪≫ b₁ ≪≫ c₁.symm) (hγ : γ = a₂ ≪≫ b₂ ≪≫ c₂.symm)
    (hs : s ≫ c₂.hom = c₁.hom ≫ t) :
    a₁.hom ≫ (b₁.hom ≫ t ≫ b₂.inv) = (β.hom ≫ s ≫ γ.inv) ≫ a₂.hom := by
  rw [hβ, hγ]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  slice_rhs 4 5 => exact hs
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end

universe u

variable {X Z X' Z' : Scheme.{u}}
  (p q : Z ⟶ X) (p' q' : Z' ⟶ X') (iX : X' ⟶ X) (iZ : Z' ⟶ Z)
  [IsOpenImmersion iX] [IsOpenImmersion iZ]
  (hp : iZ ≫ p = p' ≫ iX) (hq : iZ ≫ q = q' ≫ iX) (M : X.Modules)
  (σ : (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback q).obj M)

/-- Each actual open square factors through the ordinary geometric pullback square. -/
theorem square_component :
    (SquareBaseChange.leftSquare p p' iZ iX hp).app M =
      (Scheme.Modules.pullback p').mapIso ((Scheme.Modules.restrictFunctorIsoPullback iX).app M) ≪≫
        (Ordinary.SquareGluing.pullbackSquare p p' iX iZ hp).app M ≪≫
          ((Scheme.Modules.restrictFunctorIsoPullback iZ).app ((Scheme.Modules.pullback p).obj M)).symm := by
  rw [SquareNormalization.leftSquare_eq_standard]
  apply Iso.ext
  rfl

/-- Gluing on the actual pulled-back sheaf, using standard geometric composition maps. -/
def pullbackGluing :
    (Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback iX).obj M) ≅
      (Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback iX).obj M) :=
  (Ordinary.SquareGluing.pullbackSquare p p' iX iZ hp).app M ≪≫
    (Scheme.Modules.pullback iZ).mapIso σ ≪≫
      ((Ordinary.SquareGluing.pullbackSquare q q' iX iZ hq).app M).symm

/-- The restriction-to-pullback isomorphism retains the full original gluing morphism. -/
theorem compatible :
    (Scheme.Modules.pullback p').map ((Scheme.Modules.restrictFunctorIsoPullback iX).app M).hom ≫
      (pullbackGluing p q p' q' iX iZ hp hq M σ).hom =
    (CechInvariant.gluing p q p' q' iX iZ hp hq M σ).hom ≫
      (Scheme.Modules.pullback q').map ((Scheme.Modules.restrictFunctorIsoPullback iX).app M).hom := by
  exact iso_transition_square
    ((Scheme.Modules.pullback p').mapIso ((Scheme.Modules.restrictFunctorIsoPullback iX).app M))
    ((Scheme.Modules.pullback q').mapIso ((Scheme.Modules.restrictFunctorIsoPullback iX).app M))
    ((Ordinary.SquareGluing.pullbackSquare p p' iX iZ hp).app M)
    ((Ordinary.SquareGluing.pullbackSquare q q' iX iZ hq).app M)
    ((Scheme.Modules.restrictFunctorIsoPullback iZ).app ((Scheme.Modules.pullback p).obj M))
    ((Scheme.Modules.restrictFunctorIsoPullback iZ).app ((Scheme.Modules.pullback q).obj M))
    ((SquareBaseChange.leftSquare p p' iZ iX hp).app M)
    ((SquareBaseChange.leftSquare q q' iZ iX hq).app M)
    ((Scheme.Modules.restrictFunctor iZ).map σ.hom) ((Scheme.Modules.pullback iZ).map σ.hom)
    (square_component p p' iX iZ hp M) (square_component q q' iX iZ hq M)
    ((Scheme.Modules.restrictFunctorIsoPullback iZ).hom.naturality σ.hom)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.GluingNormalization
