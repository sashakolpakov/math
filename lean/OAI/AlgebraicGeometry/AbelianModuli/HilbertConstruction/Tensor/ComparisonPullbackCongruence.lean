import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionTensorComparison

/-! # Comparison Pullback Congruence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ComparisonPullbackCongruence

noncomputable section

/-! Equality of the pullback map, coefficient maps, and test open preserves bijectivity of the actual tensor comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem moduleSectionTensorComparisonApp_bijective_congr
    {X Y : Scheme.{u}} {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {a a' : Y ⟶ X} (ha : a = a') {f f' : R →+* Γ(X, ⊤)} (hf : f = f') (M : X.Modules)
    {q q' : B →+* Γ(Y, ⊤)} (hq : q = q')
    (hc : q.comp (algebraMap R B) = a.appTop.hom.comp f)
    (hc' : q'.comp (algebraMap R B) = a'.appTop.hom.comp f') {U V : X.Opens} (hU : U = V) :
    Function.Bijective (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a f M q hc U) ↔
      Function.Bijective (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a' f' M q' hc' V) := by
  subst a'
  subst f'
  subst q'
  subst V
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ComparisonPullbackCongruence
