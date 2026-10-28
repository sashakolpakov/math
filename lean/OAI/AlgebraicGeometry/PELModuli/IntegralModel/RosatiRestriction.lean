import OAI.AlgebraicGeometry.PELModuli.IntegralModel.RosatiIsoTransport
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionScheme
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RosatiBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

/-! # Rosati Restriction -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.RosatiRestriction

noncomputable section

section

/-! The actual integral-action restriction functor preserves Rosati
compatibility on arbitrary test schemes. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence
variable {S S' : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}

def polarizedPullbackCongrIso (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (f h : S' ⟶ S) (w : f = h) : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback f) (A.pullback h) := by
  cases w
  exact AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.refl _

theorem polarizedPullbackCongrIso_abelian (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (f h : S' ⟶ S) (w : f = h) :
    (polarizedPullbackCongrIso A f h w).abelian = A.abelian.pullbackCongrIso f h w := by
  cases w
  rfl

variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) {T U : Over S}

def polarizedRestrictionIso (f : T ⟶ U) :
    AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso ((A.pullback U.hom).pullback f.left) (A.pullback T.hom) :=
  (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A U.hom f.left).trans
    (polarizedPullbackCongrIso A (f.left ≫ U.hom) T.hom f.w)

theorem polarizedRestrictionIso_abelian (f : T ⟶ U) :
    (polarizedRestrictionIso A f).abelian = EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A.abelian f := by
  change (A.abelian.pullbackCompIso U.hom f.left).symm ≪≫
    (polarizedPullbackCongrIso A (f.left ≫ U.hom) T.hom f.w).abelian = _
  rw [polarizedPullbackCongrIso_abelian]
  rfl

theorem rosati_restrictIntegralAction
    {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback U.hom).abelian)
    (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback U.hom) ρ) (f : T ⟶ U) :
    AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback T.hom) (Integral.ActionScheme.restrictIntegralAction A.abelian ρ f) := by
  apply RosatiIsoTransport.rosati_of_polarized_iso (polarizedRestrictionIso A f) (ρ.pullback f.left)
    (Integral.ActionScheme.restrictIntegralAction A.abelian ρ f) _
    (AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation.pullback (A.pullback U.hom) ρ hρ f.left)
  intro a
  rw [polarizedRestrictionIso_abelian]
  change (EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A.abelian f).hom ≫
    ((EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A.abelian f).inv ≫
      (Over.pullback f.left).map (ρ.map a) ≫ (EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A.abelian f).hom) =
    (Over.pullback f.left).map (ρ.map a) ≫ (EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A.abelian f).hom
  rw [Iso.hom_inv_id_assoc]

end

/-! Actual polarized comparison isomorphisms reflect, as well as
preserve, Rosati compatibility. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

theorem rosati_iff_of_polarized_iso
    {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    {A B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S} (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A B)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B.abelian)
    (ha : ∀ a, e.abelian.hom ≫ σ.map a = ρ.map a ≫ e.abelian.hom) :
    AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ ↔ AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation B σ := by
  refine ⟨RosatiIsoTransport.rosati_of_polarized_iso e ρ σ ha, RosatiIsoTransport.rosati_of_polarized_iso e.symm σ ρ ?_⟩
  intro a
  change e.abelian.inv ≫ ρ.map a = σ.map a ≫ e.abelian.inv
  apply (cancel_epi e.abelian.hom).mp
  rw [e.abelian.hom_inv_id_assoc, ← Category.assoc, ha, Category.assoc,
    e.abelian.hom_inv_id, Category.comp_id]

theorem rosati_restrictIntegralAction_iff
    {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) {T U : Over S}
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback U.hom).abelian)
    (f : T ⟶ U) :
    AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback T.hom) (Integral.ActionScheme.restrictIntegralAction A.abelian ρ f) ↔
      AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation ((A.pullback U.hom).pullback f.left) (ρ.pullback f.left) := by
  apply (rosati_iff_of_polarized_iso (polarizedRestrictionIso A f) (ρ.pullback f.left)
    (Integral.ActionScheme.restrictIntegralAction A.abelian ρ f) ?_).symm
  intro a
  rw [polarizedRestrictionIso_abelian]
  change (EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A.abelian f).hom ≫
    ((EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A.abelian f).inv ≫
      (Over.pullback f.left).map (ρ.map a) ≫ (EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A.abelian f).hom) =
    (Over.pullback f.left).map (ρ.map a) ≫ (EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A.abelian f).hom
  rw [Iso.hom_inv_id_assoc]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.RosatiRestriction
