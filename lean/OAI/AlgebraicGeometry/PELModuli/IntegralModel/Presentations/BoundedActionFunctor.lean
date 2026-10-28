import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionFunctor
import Mathlib.CategoryTheory.Subfunctor.Image

/-! # Bounded Action Functor -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.BoundedActionFunctor

noncomputable section

/-! Identify the actual bounded integral-action functor with Presentations's concrete
solution functor. The bound is precisely Presentations's native graph Hilbert predicate. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E)
  (hc : ∀ s : S, IsUnit (D.conductor : S.presheaf.stalk s))
  (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (A.scheme ⨯ A.scheme))
  (P : Fin 1 → Polynomial ℚ) (L : HilbertScheme.Presentations.Loci.Core.HilbertHomLoci A.scheme A.scheme B 1 P)
  (M : HilbertScheme.Presentations.Loci.Core.EndomorphismEquationLoci A.scheme B 1 P L (Generator.EndomorphismFamilies.e34IntegralGeneratorEquations A D hc))

def boundedIntegralActions : Subfunctor (Integral.ActionFunctor.integralActionFunctor A E) where
  obj T := {ρ | (Integral.ActionFunctor.integralGeneratorTupleMap A D).app T ρ ∈ M.endLocus.obj T}
  map {T U} f ρ hρ := by
    have h := M.endLocus.map f hρ
    have hn := ConcreteCategory.congr_hom ((Integral.ActionFunctor.integralGeneratorTupleMap A D).naturality f) ρ
    change (Integral.ActionFunctor.integralGeneratorTupleMap A D).app U ((Integral.ActionFunctor.integralActionFunctor A E).map f ρ) ∈ M.endLocus.obj U
    change (Integral.ActionFunctor.integralGeneratorTupleMap A D).app U ((Integral.ActionFunctor.integralActionFunctor A E).map f ρ) =
      (HilbertScheme.Presentations.Endomorphisms.Core.endomorphismTuples A.scheme 1).map f ((Integral.ActionFunctor.integralGeneratorTupleMap A D).app T ρ) at hn
    rw [hn]
    exact h

theorem boundedIntegralActions_mem (T : Over S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback T.hom)) :
    ρ ∈ (boundedIntegralActions A D hc B P L M).obj (op T) ↔
      HilbertScheme.Presentations.Has.Core.HasGraphPolynomials A.scheme A.scheme 1 B P
        ((HilbertScheme.Presentations.Endomorphisms.Core.forgetGroupLaw A.scheme 1).app (op T) ((Integral.ActionFunctor.integralGeneratorTupleMap A D).app (op T) ρ)) :=
  M.end_mem T _

theorem integralGeneratorTuple_satisfies (T : Over S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback T.hom)) :
    HilbertScheme.Presentations.Endomorphisms.Core.SatisfiesEquations (Generator.EndomorphismFamilies.e34IntegralGeneratorEquations A D hc)
      ((Integral.ActionFunctor.integralGeneratorTupleMap A D).app (op T) ρ) := by
  apply (Generator.EndomorphismFamilies.e34IntegralGeneratorEquations_iff A D hc T _).mpr
  rw [Integral.ActionFunctor.primitive_integralGeneratorTuple]
  exact D.generator_conditions_of_action (A.pullback T.hom) ρ

theorem integralGeneratorTuple_mem_solution (T : Over S)
    (ρ : (boundedIntegralActions A D hc B P L M).toFunctor.obj (op T)) :
    (Integral.ActionFunctor.integralGeneratorTupleMap A D).app (op T) ρ.val ∈ M.solutionLocus.obj (op T) :=
  (M.solution_mem T _).mpr ⟨(M.end_mem T _).mp ρ.property,
    integralGeneratorTuple_satisfies A D hc T ρ.val⟩

def boundedActionToSolutions : (boundedIntegralActions A D hc B P L M).toFunctor ⟶
    M.solutionLocus.toFunctor :=
  Subfunctor.lift ((boundedIntegralActions A D hc B P L M).ι ≫ Integral.ActionFunctor.integralGeneratorTupleMap A D) (by
    intro T f hf
    obtain ⟨ρ, rfl⟩ := hf
    exact integralGeneratorTuple_mem_solution A D hc B P L M T.unop ρ)

theorem boundedActionToSolutions_val (T : Over S)
    (ρ : (boundedIntegralActions A D hc B P L M).toFunctor.obj (op T)) :
    ((boundedActionToSolutions A D hc B P L M).app (op T) ρ).val =
      (Integral.ActionFunctor.integralGeneratorTupleMap A D).app (op T) ρ.val := rfl

theorem boundedActionToSolutions_bijective (T : Over S) :
    Function.Bijective ((boundedActionToSolutions A D hc B P L M).app (op T)) := by
  constructor
  · intro ρ σ h
    apply Subtype.ext
    apply Integral.ActionFunctor.integralGeneratorTupleMap_injective A D hc T
    simpa only [boundedActionToSolutions_val] using congrArg Subtype.val h
  · intro f
    have hf := (M.solution_mem T f.val).mp f.property
    have hu := (Generator.EndomorphismFamilies.e34IntegralGeneratorEquations_iff A D hc T f.val).mp hf.2
    have hct (t : T.left) : IsUnit (D.conductor : T.left.presheaf.stalk t) := by
      simpa only [map_natCast] using (hc (T.hom t)).map (T.hom.stalkMap t).hom
    obtain ⟨ρ, hρ, _⟩ := D.existsUnique_integral_action_of_generator_conditions
      (A.pullback T.hom) ((EndomorphismBridge.EndomorphismFamilies.e34PrimitiveEndomorphism A).app (op T) f.val) hct hu
    have htuple : (Integral.ActionFunctor.integralGeneratorTupleMap A D).app (op T) ρ = f.val := by
      apply Generator.EndomorphismFamilies.e34Primitive_injective A T
      rw [Integral.ActionFunctor.primitive_integralGeneratorTuple]
      exact Finite.Actions.GroupEndRing.ext (A.pullback T.hom) hρ
    have hbound : ρ ∈ (boundedIntegralActions A D hc B P L M).obj (op T) := by
      change (Integral.ActionFunctor.integralGeneratorTupleMap A D).app (op T) ρ ∈ M.endLocus.obj (op T)
      rw [htuple]
      exact (M.end_mem T f.val).mpr hf.1
    refine ⟨⟨ρ, hbound⟩, Subtype.ext ?_⟩
    exact (boundedActionToSolutions_val A D hc B P L M T ⟨ρ, hbound⟩).trans htuple

def boundedIntegralActionIso : (boundedIntegralActions A D hc B P L M).toFunctor ≅
    M.solutionLocus.toFunctor :=
  NatIso.ofComponents
    (fun T => (Equiv.ofBijective _ (boundedActionToSolutions_bijective A D hc B P L M T.unop)).toIso)
    (by intro T U f; exact (boundedActionToSolutions A D hc B P L M).naturality f)

def boundedIntegralActionRepresentation : yoneda.obj M.solutionScheme ≅
    (boundedIntegralActions A D hc B P L M).toFunctor :=
  M.solutionEquivalence ≪≫ (boundedIntegralActionIso A D hc B P L M).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.BoundedActionFunctor
