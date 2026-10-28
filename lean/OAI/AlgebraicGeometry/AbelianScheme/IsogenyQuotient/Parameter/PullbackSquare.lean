import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterLineNaturality

/-! # Pullback Square -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.PullbackSquare.Construction

noncomputable section

/-! Restriction between parameterized group schemes is the actual
Cartesian square over the map of parameter schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterLineNaturality.Construction.KernelCharacters

universe u

theorem parameterPullbackMap_isPullback {S : Scheme.{u}} (B : Over S)
    {P Q : Over S} (t : P ⟶ Q) :
    IsPullback (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B t) (pullback.snd B.hom P.hom)
      (pullback.snd B.hom Q.hom) t.left := by
  apply IsPullback.of_right (t := IsPullback.of_hasPullback B.hom Q.hom)
  · rw [CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap_fst, t.w]
    exact IsPullback.of_hasPullback B.hom P.hom
  · exact CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap_snd B t

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.PullbackSquare.Construction
