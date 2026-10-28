import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ActionBaseChangeComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionFunctor

/-! # Integral Action Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.IntegralActionBaseChange

noncomputable section

/-! A natural equivalence between the integral action functor after base
change and the restriction of the original action functor. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

namespace ActionBaseChange
variable {S B : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (b : B ⟶ S)

def endTransport (T : Over B) : Finite.Actions.GroupEndRing ((A.pullback b).pullback T.hom) →+*
    Finite.Actions.GroupEndRing (A.pullback ((Over.map b).obj T).hom) := Finite.Actions.GroupEndRing.transport (ActionBaseChangeComparison.ActionBaseChange.groupIso A b T)

@[reassoc]
theorem endTransport_fst (T : Over B) (r : Finite.Actions.GroupEndRing ((A.pullback b).pullback T.hom)) :
    EndomorphismFamiliesId.EndomorphismFamilies.endHom A (endTransport A b T r) ≫ pullback.fst A.scheme.hom (T.hom ≫ b) =
      (ActionBaseChangeComparison.ActionBaseChange.schemeIso A b T).inv ≫ EndomorphismFamiliesId.EndomorphismFamilies.endHom (A.pullback b) r ≫
        pullback.fst (A.pullback b).scheme.hom T.hom ≫ pullback.fst A.scheme.hom b := by
  change ((ActionBaseChangeComparison.ActionBaseChange.schemeIso A b T).inv ≫ EndomorphismFamiliesId.EndomorphismFamilies.endHom (A.pullback b) r ≫ (ActionBaseChangeComparison.ActionBaseChange.schemeIso A b T).hom) ≫ _ = _
  rw [Category.assoc, Category.assoc, ActionBaseChangeComparison.ActionBaseChange.schemeIso_hom_fst]

theorem endTransport_natural {T U : Over B} (f : T ⟶ U)
    (r : Finite.Actions.GroupEndRing ((A.pullback b).pullback U.hom)) :
    EndomorphismFamiliesId.EndomorphismFamilies.restrict A ((Over.map b).map f) (endTransport A b U r) =
      endTransport A b T (EndomorphismFamiliesId.EndomorphismFamilies.restrict (A.pullback b) f r) := by
  apply EndomorphismFamiliesId.EndomorphismFamilies.ext_of_fst A
  rw [EndomorphismFamiliesId.EndomorphismFamilies.restrict_fst]
  change EndomorphismFamiliesId.EndomorphismFamilies.familyMap A ((Over.map b).map f) ≫ EndomorphismFamiliesId.EndomorphismFamilies.endHom A (endTransport A b U r) ≫
      pullback.fst A.scheme.hom (U.hom ≫ b) =
    EndomorphismFamiliesId.EndomorphismFamilies.endHom A (endTransport A b T (EndomorphismFamiliesId.EndomorphismFamilies.restrict (A.pullback b) f r)) ≫
      pullback.fst A.scheme.hom (T.hom ≫ b)
  rw [endTransport_fst, endTransport_fst]
  rw [← Category.assoc (EndomorphismFamiliesId.EndomorphismFamilies.endHom (A.pullback b) (EndomorphismFamiliesId.EndomorphismFamilies.restrict (A.pullback b) f r)), EndomorphismFamiliesId.EndomorphismFamilies.restrict_fst]
  simp only [Category.assoc]
  rw [← Category.assoc (EndomorphismFamiliesId.EndomorphismFamilies.familyMap A ((Over.map b).map f)), ActionBaseChangeComparison.ActionBaseChange.familyMap_comparison]
  simp only [Category.assoc]

variable {R : Type} [CommRing R]

def actionEquiv (T : Over B) : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R ((A.pullback b).pullback T.hom) ≃
    AbelianModuli.ReferenceFamily.ActionData.IntegralAction R (A.pullback ((Over.map b).obj T).hom) :=
  ActionBaseChangeComparison.integralActionTransportEquiv (ActionBaseChangeComparison.ActionBaseChange.groupIso A b T)

theorem actionEquiv_natural {T U : Over B} (f : T ⟶ U)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R ((A.pullback b).pullback U.hom)) :
    actionEquiv A b T (ActionScheme.restrictIntegralAction (A.pullback b) ρ f) =
      ActionScheme.restrictIntegralAction A (actionEquiv A b U ρ) ((Over.map b).map f) := by
  apply ActionScheme.ringHomOfIntegralAction_injective
  apply RingHom.ext
  intro r
  change endTransport A b T (EndomorphismFamiliesId.EndomorphismFamilies.restrict (A.pullback b) f
      (Finite.Actions.ringHomOfIntegralAction ((A.pullback b).pullback U.hom) ρ r)) =
    EndomorphismFamiliesId.EndomorphismFamilies.restrict A ((Over.map b).map f) (endTransport A b U
      (Finite.Actions.ringHomOfIntegralAction ((A.pullback b).pullback U.hom) ρ r))
  exact (endTransport_natural A b f _).symm

def integralActionFunctorIso (E : Type) [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] : ActionFunctor.integralActionFunctor (A.pullback b) E ≅
      (Over.map b).op ⋙ ActionFunctor.integralActionFunctor A E :=
  NatIso.ofComponents (fun T => (actionEquiv (R := NumberField.RingOfIntegers E) A b T.unop).toIso)
    (by
      intro T U f
      apply ConcreteCategory.hom_ext
      intro ρ
      exact actionEquiv_natural A b f.unop ρ)

end ActionBaseChange

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.IntegralActionBaseChange
