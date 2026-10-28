import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionScheme
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Generator

/-! # Action Functor -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionFunctor

noncomputable section

/-! The actual integral-action functor and its faithful primitive-generator
map into Presentations's endomorphism tuples. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (E : Type) [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]

def integralActionFunctor : (Over S)ᵒᵖ ⥤ Type where
  obj T := AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback T.unop.hom)
  map f := ↾fun ρ => ActionScheme.restrictIntegralAction A ρ f.unop
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro ρ
    exact ActionScheme.restrictIntegralAction_id A T.unop ρ
  map_comp f h := by
    apply ConcreteCategory.hom_ext
    intro ρ
    exact ActionScheme.restrictIntegralAction_comp A h.unop f.unop ρ

variable {E} (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E)

def integralPrimitiveEndomorphism : integralActionFunctor A E ⟶
    (EndomorphismFamiliesId.EndomorphismFamilies.endomorphismFunctor A ⋙ forget RingCat) where
  app T := ↾fun ρ => Finite.Actions.ringHomOfIntegralAction (A.pullback T.unop.hom) ρ D.generator
  naturality {T U} f := by
    apply ConcreteCategory.hom_ext
    intro ρ
    exact RingHom.congr_fun (ActionScheme.restrictIntegralAction_ringHom A ρ f.unop) D.generator

def integralGeneratorTupleMap : integralActionFunctor A E ⟶
    HilbertScheme.Presentations.Endomorphisms.Core.endomorphismTuples A.scheme 1 where
  app T := ↾fun ρ => Presentations.Generator.EndomorphismFamilies.e34GeneratorTuple A T.unop
    ((integralPrimitiveEndomorphism A D).app T ρ)
  naturality {T U} f := by
    apply ConcreteCategory.hom_ext
    intro ρ
    funext i
    apply Subtype.ext
    change EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A U.unop
        (((integralPrimitiveEndomorphism A D).app U
          ((integralActionFunctor A E).map f ρ)).hom (A.pullback U.unop.hom)) = _
    have h := ConcreteCategory.congr_hom ((integralPrimitiveEndomorphism A D).naturality f) ρ
    change (integralPrimitiveEndomorphism A D).app U ((integralActionFunctor A E).map f ρ) =
      EndomorphismFamiliesId.EndomorphismFamilies.restrict A f.unop ((integralPrimitiveEndomorphism A D).app T ρ) at h
    rw [h]
    exact EndomorphismHom.EndomorphismFamilies.relativeHom_restrict A f.unop _

@[simp] theorem primitive_integralGeneratorTuple (T : Over S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback T.hom)) :
    (Presentations.EndomorphismBridge.EndomorphismFamilies.e34PrimitiveEndomorphism A).app (op T)
      ((integralGeneratorTupleMap A D).app (op T) ρ) =
        Finite.Actions.ringHomOfIntegralAction (A.pullback T.hom) ρ D.generator :=
  Presentations.Generator.EndomorphismFamilies.e34Primitive_generatorTuple A T _

theorem integralGeneratorTupleMap_injective
    (hc : ∀ s : S, IsUnit (D.conductor : S.presheaf.stalk s)) (T : Over S) :
    Function.Injective ((integralGeneratorTupleMap A D).app (op T)) := by
  intro ρ σ h
  have hgen := congrArg ((Presentations.EndomorphismBridge.EndomorphismFamilies.e34PrimitiveEndomorphism A).app (op T)) h
  rw [primitive_integralGeneratorTuple, primitive_integralGeneratorTuple] at hgen
  apply D.integral_action_eq_of_generator (A.pullback T.hom) ρ σ
  · intro t
    simpa only [map_natCast] using (hc (T.hom t)).map (T.hom.stalkMap t).hom
  · exact congrArg (Finite.Actions.GroupEndRing.hom (A.pullback T.hom)) hgen

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionFunctor
