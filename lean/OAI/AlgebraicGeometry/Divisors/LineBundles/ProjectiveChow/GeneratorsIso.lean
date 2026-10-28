import OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.Filtration
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SeparatedChowIso

/-! # Generators Iso -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.GeneratorsIso.BundleCycles

noncomputable section

/-! Projective Chow generators use only the actual isomorphism
class of the line bundle and the actual projection morphism. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    [E.IsSeparated] (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r)
    {L M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E} (e : L.sheaf ≅ M.sheaf)

include e in
theorem projectiveChowComponent_lineBundleIso (d k i : ℕ) (hd : k + r = d + i) :
    Filtration.BundleCycles.projectiveChowComponent p f r hp L d k i hd = Filtration.BundleCycles.projectiveChowComponent p f r hp M d k i hd := by
  unfold Filtration.BundleCycles.projectiveChowComponent
  rw [LineBundle.SeparatedChowIso.Cycles.separatedLineBundleChowPower_iso e]

include e in
theorem projectiveChowGenerated_lineBundleIso (d : ℕ) :
    Filtration.BundleCycles.projectiveChowGenerated p f r hp L d = Filtration.BundleCycles.projectiveChowGenerated p f r hp M d := by
  unfold Filtration.BundleCycles.projectiveChowGenerated
  simp only [projectiveChowComponent_lineBundleIso p f r hp e]

theorem projectiveChowGenerated_projection_congr (q : E ⟶ X) [Smooth q] [GeometricallyIntegral q]
    (h : p = q) (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank q r) (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E)
    (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) d) :
    DimensionChow.BundleCycles.dimensionChowTransport (congrArg (fun t => t ≫ f) h) d α ∈ Filtration.BundleCycles.projectiveChowGenerated q f r hq L d ↔
      α ∈ Filtration.BundleCycles.projectiveChowGenerated p f r hp L d := by
  subst q
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.GeneratorsIso.BundleCycles
