import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyFactorizationIs

/-! # Quotient Action Base -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientActionBase.Construction

noncomputable section

/-!
The endomorphism action on an isogeny quotient is constructed by fpqc
descent. Stability is tested on the entire scheme kernel, not only its
geometric points. Ring identities follow by epimorphic cancellation.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u v

variable {S : Scheme.{u}} {g : ℕ}
variable {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
variable {R : Type v} [CommRing R]

/-- The actual kernel is stable under the specified integral action. -/
def ActionStableKernel (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A)
    (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) : Prop :=
  ∀ (r : R) (T : Over S) (x : T ⟶ A.scheme),
    x ≫ p.hom = 1 → (x ≫ ρ.map r) ≫ p.hom = 1

theorem quotientAction_exists
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
    (hstable : ActionStableKernel ρ p) (r : R) :
    ∃! d : B.scheme ⟶ B.scheme,
      IsMonHom d ∧ p.hom ≫ d = ρ.map r ≫ p.hom := by
  apply PELModuli.IntegralModel.IsogenyFactorizationIs.IsogenyFactorization.fpqc_group_hom_descent p.hom (ρ.map r ≫ p.hom)
  intro T x hx
  exact (Category.assoc x (ρ.map r) p.hom).symm.trans (hstable r T x hx)

/-- Construct all quotient endomorphisms and prove that they form a
unital ring action. No descended action is supplied as an assumption. -/
def quotientAction
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
    (hstable : ActionStableKernel ρ p) : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R B := by
  let d := fun r => Classical.choose (quotientAction_exists ρ p hstable r)
  have hd (r : R) : IsMonHom (d r) ∧ p.hom ≫ d r = ρ.map r ≫ p.hom :=
    (Classical.choose_spec (quotientAction_exists ρ p hstable r)).1
  have : EffectiveEpi p.hom := PELModuli.IntegralModel.IsogenyFactorizationIs.IsogenyFactorization.effectiveEpi_over_of_fpqc p.hom
  refine {
    map := d
    preservesGroup := fun r => (hd r).1
    map_zero := ?_
    map_one := ?_
    map_add := ?_
    map_mul := ?_ }
  · apply (cancel_epi p.hom).mp
    rw [(hd 0).2, ρ.map_zero, MonObj.one_comp, MonObj.comp_one]
  · apply (cancel_epi p.hom).mp
    rw [(hd 1).2, ρ.map_one, Category.id_comp, Category.comp_id]
  · intro r t
    apply (cancel_epi p.hom).mp
    rw [MonObj.comp_mul, (hd (r + t)).2, (hd r).2, (hd t).2,
      ρ.map_add, MonObj.mul_comp]
  · intro r t
    apply (cancel_epi p.hom).mp
    rw [(hd (r * t)).2, ρ.map_mul]
    calc
      (ρ.map t ≫ ρ.map r) ≫ p.hom = ρ.map t ≫ (ρ.map r ≫ p.hom) :=
        Category.assoc _ _ _
      _ = ρ.map t ≫ (p.hom ≫ d r) := by rw [(hd r).2]
      _ = (ρ.map t ≫ p.hom) ≫ d r := (Category.assoc _ _ _).symm
      _ = (p.hom ≫ d t) ≫ d r := by rw [(hd t).2]
      _ = p.hom ≫ (d t ≫ d r) := Category.assoc _ _ _

theorem quotientAction_intertwines
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
    (hstable : ActionStableKernel ρ p) (r : R) :
    p.hom ≫ (quotientAction ρ p hstable).map r = ρ.map r ≫ p.hom :=
  (Classical.choose_spec (quotientAction_exists ρ p hstable r)).1.2

/-- Uniqueness of the constructed action, expressed on its actual maps. -/
theorem quotientAction_unique
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
    (hstable : ActionStableKernel ρ p)
    (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R B)
    (hσ : ∀ r, p.hom ≫ σ.map r = ρ.map r ≫ p.hom) (r : R) :
    σ.map r = (quotientAction ρ p hstable).map r :=
  (Classical.choose_spec (quotientAction_exists ρ p hstable r)).2 (σ.map r)
    ⟨σ.preservesGroup r, hσ r⟩

/-- The constructed intertwining identity specializes by genuine pullback. -/
theorem quotientAction_baseChange_intertwines
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
    (hstable : ActionStableKernel ρ p) {T : Scheme.{u}} (f : T ⟶ S) (r : R) :
    (Over.pullback f).map p.hom ≫
        ((quotientAction ρ p hstable).pullback f).map r =
      (ρ.pullback f).map r ≫ (Over.pullback f).map p.hom := by
  change (Over.pullback f).map p.hom ≫
    (Over.pullback f).map ((quotientAction ρ p hstable).map r) =
    (Over.pullback f).map (ρ.map r) ≫ (Over.pullback f).map p.hom
  simpa only [← Functor.map_comp] using
    congrArg (Over.pullback f).map (quotientAction_intertwines ρ p hstable r)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientActionBase.Construction
