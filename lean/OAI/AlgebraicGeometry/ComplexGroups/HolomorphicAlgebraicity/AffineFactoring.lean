import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SchemePointSeparation

/-! # Affine Factoring -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AffineFactoring.Constructions.Algebraization

noncomputable section

/-!
# Simultaneous affine neighborhoods for two scheme maps

Two maps into specified open charts factor through those charts after
restricting to an affine open neighborhood of a given complex point.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set

def openImmersionLiftOver
    {X Y U : Over Foundations.Scheme.ProjectiveSpace.complexBase} (u : U ⟶ Y) [IsOpenImmersion u.left]
    (f : X ⟶ Y) (h : range f.left ⊆ range u.left) : X ⟶ U :=
  Over.homMk (IsOpenImmersion.lift u.left f.left h) (by
    rw [← u.w, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact f.w)

theorem openImmersionLiftOver_fac
    {X Y U : Over Foundations.Scheme.ProjectiveSpace.complexBase} (u : U ⟶ Y) [IsOpenImmersion u.left]
    (f : X ⟶ Y) (h : range f.left ⊆ range u.left) :
    openImmersionLiftOver u f h ≫ u = f := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac u.left f.left h

theorem exists_affine_neighborhood_factoring_two_maps
    {X Y Z U V : Over Foundations.Scheme.ProjectiveSpace.complexBase} (a : X ⟶ Y) (b : X ⟶ Z)
    (u : U ⟶ Y) (v : V ⟶ Z) [IsOpenImmersion u.left] [IsOpenImmersion v.left]
    (q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (ha : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a q ∈ range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map u))
    (hb : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map b q ∈ range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map v)) :
    ∃ (T : Over Foundations.Scheme.ProjectiveSpace.complexBase) (k : T ⟶ X) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints T)
      (a' : T ⟶ U) (b' : T ⟶ V),
      IsAffine T.left ∧ IsOpenImmersion k.left ∧
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k p = q ∧ a' ≫ u = k ≫ a ∧ b' ≫ v = k ≫ b := by
  let W : X.left.Opens := (a.left ⁻¹ᵁ u.left.opensRange) ⊓ (b.left ⁻¹ᵁ v.left.opensRange)
  have hqW : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying q ∈ W := by
    obtain ⟨qa, hqa⟩ := ha
    obtain ⟨qb, hqb⟩ := hb
    exact ⟨⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying qa, congrArg ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying hqa⟩,
      ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying qb, congrArg ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying hqb⟩⟩
  obtain ⟨W₀, hW₀, hqW₀, hsub⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.left.isBasis_affineOpens) hqW
  change X.left.Opens at W₀
  let T := Over.mk (W₀.ι ≫ X.hom)
  let k : T ⟶ X := Over.homMk W₀.ι rfl
  have hT : IsAffine T.left := hW₀
  have hk : IsOpenImmersion k.left := inferInstanceAs (IsOpenImmersion W₀.ι)
  have ha' : range (k ≫ a).left ⊆ range u.left := by
    rintro _ ⟨x, rfl⟩
    exact (hsub x.property).1
  have hb' : range (k ≫ b).left ⊆ range v.left := by
    rintro _ ⟨x, rfl⟩
    exact (hsub x.property).2
  obtain ⟨p, hp⟩ := Foundations.Scheme.ImmersionComplexPoints.surjectiveOnStalks_relativeFieldPoint_existsLift k q
    (⊥ : PrimeSpectrum ℂ) ⟨⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying q, hqW₀⟩, rfl⟩
  exact ⟨T, k, p, openImmersionLiftOver u (k ≫ a) ha', openImmersionLiftOver v (k ≫ b) hb',
    hT, hk, hp, openImmersionLiftOver_fac u (k ≫ a) ha', openImmersionLiftOver_fac v (k ≫ b) hb'⟩

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AffineFactoring.Constructions.Algebraization
