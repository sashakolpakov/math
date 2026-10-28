import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.IntrinsicActiveLift
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FactorTheta
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductRepresentationExt
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SmoothExtensionElimination

/-! # Factor Smoothness -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FactorSmoothness

noncomputable section

/-! The original source active/away representation equals the smooth
native extension. In particular its actual away stabilizers are open. -/

attribute [local instance 2000] Subgroup.toGroup Prod.instGroup
open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FactorTheta.CM.RationalWeilFactorization

namespace CM

private theorem functions_of_active_and_rational
    {R A B H : Type*} [MulOneClass A] [MulOneClass B] [Group H]
    (r : R → A × B) (hb : Function.Surjective (fun g => (r g).2))
    (S T : A × B → H) (hSmul : ∀ a b, S (a * b) = S a * S b)
    (hTmul : ∀ a b, T (a * b) = T a * T b)
    (hr : ∀ g, S (r g) = T (r g)) (ha : ∀ a, S (a, 1) = T (a, 1)) : S = T := by
  have haway (b : B) : S (1, b) = T (1, b) := by
    obtain ⟨g, hg⟩ := hb b
    have hp : ((r g).1, (1 : B)) * (1, b) = r g := by
      apply Prod.ext
      · simp
      · simpa using hg.symm
    apply mul_left_cancel (a := S ((r g).1, 1))
    calc
      _ = S (r g) := (hSmul _ _).symm.trans (congrArg S hp)
      _ = T (r g) := hr g
      _ = T ((r g).1, 1) * T (1, b) := (congrArg T hp.symm).trans (hTmul _ _)
      _ = _ := congrArg (fun h : H => h * T (1, b)) (ha (r g).1).symm
  funext x
  obtain ⟨a, b⟩ := x
  have hp : (a, b) = (a, (1 : B)) * (1, b) := by simp
  rw [hp, hSmul, hTmul, ha, haway]

private theorem smooth_of_function_eq {G H A V : Type*}
    [TopologicalSpace G] [TopologicalSpace H]
    (act : A → V → V) (rho : H → A)
    (hrho : ∀ v : V, IsOpen {h | act (rho h) v = v})
    (f : G → H) (hf : Continuous f) (sigma : G → A)
    (he : sigma = fun g => rho (f g)) (v : V) :
    IsOpen {g | act (sigma g) v = v} := by
  subst sigma
  exact (hrho v).preimage hf

local instance factorAwayGroup (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
    {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
    (L : GeometricSource.CM.LinePeriod E B places d)
    {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q]) : Group (FactorTheta.CM.RationalWeilFactorization.Away E L f) := Subgroup.toGroup (FactorTheta.CM.RationalWeilFactorization.Away E L f)
local instance factorAwayMulOneClass (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
    {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
    (L : GeometricSource.CM.LinePeriod E B places d)
    {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q]) : MulOneClass (FactorTheta.CM.RationalWeilFactorization.Away E L f) :=
  SubmonoidClass.toMulOneClass (FactorTheta.CM.RationalWeilFactorization.Away E L f)
local instance factorSourceMulOneClass (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
    {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
    (L : GeometricSource.CM.LinePeriod E B places d)
    {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q]) :
    MulOneClass (Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] × FactorTheta.CM.RationalWeilFactorization.Away E L f) :=
  (show Group (Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] × FactorTheta.CM.RationalWeilFactorization.Away E L f) from Prod.instGroup).toMulOneClass

theorem active_action (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
    {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
    (L : GeometricSource.CM.LinePeriod E B places d)
    {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])
    (u : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q])
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    FactorTheta.CM.action E L f (u, 1) φ =
      (WeilData.CM.weilData E places).finite.action
        (ReferenceActiveWeil.CM.Reference.lift E L.coordinates f u) φ := by
  change (WeilData.CM.weilData E places).finite.action
    (ReferenceActiveWeil.CM.Reference.lift E L.coordinates f u * 1) φ = _
  rw [mul_one]

private theorem native_mul (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
    {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
    (L : GeometricSource.CM.LinePeriod E B places d)
    (ρ : SourceFinite.Product.CM.FiniteGroup E (OppositeCoordinates.CM.coordinates E L.coordinates) →*
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)))
    {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])
    (u v : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) (b c : FactorTheta.CM.RationalWeilFactorization.Away E L f) :
    ρ (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f (u * v, b * c)) =
      ρ (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f (u, b)) *
        ρ (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f (v, c)) :=
  (congrArg ρ ((IntrinsicActiveClosure.CM.Intrinsic.assemble E L f).map_mul'
    (u, b) (v, c))).trans
      (ρ.map_mul' (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f (u, b))
        (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f (v, c)))

private theorem rational_values (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
    {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
    (L : GeometricSource.CM.LinePeriod E B places d)
    (ρ : SourceFinite.Product.CM.FiniteGroup E (OppositeCoordinates.CM.coordinates E L.coordinates) →*
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)))
    (hr : ρ.comp (SourceAdelic.ThetaRationalTheta.CM.rational E L) = WeilData.CM.finiteAction E L)
    {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])
    (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    FactorTheta.CM.action E L f (RationalAwayTopology.CM.rational E L f γ) φ =
      ρ (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f
        (RationalAwayTopology.CM.rational E L f γ)) φ := by
  have he := congrArg ρ (IntrinsicActiveClosure.CM.Intrinsic.rational E L f γ)
  have hv := (DFunLike.congr_fun he φ).trans (RationalOscillator.CM.action E L ρ hr γ φ)
  exact (FactorTheta.CM.rational_action E L f γ φ).trans hv.symm

private theorem active_values (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
    {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
    (L : GeometricSource.CM.LinePeriod E B places d)
    (ρ : SourceFinite.Product.CM.FiniteGroup E (OppositeCoordinates.CM.coordinates E L.coordinates) →*
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)))
    (hρ : ∀ φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places), IsOpen {g | ρ g φ = φ})
    (hr : ρ.comp (SourceAdelic.ThetaRationalTheta.CM.rational E L) = WeilData.CM.finiteAction E L)
    {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])
    (u : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q])
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    FactorTheta.CM.action E L f (u, 1) φ =
      ρ (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f (u, 1)) φ :=
  (active_action E L f u φ).trans
    (IntrinsicActiveLift.CM.Intrinsic.source_action E L ρ hρ hr f u φ).symm

theorem hom (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
    {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
    (L : GeometricSource.CM.LinePeriod E B places d)
    (ρ : SourceFinite.Product.CM.FiniteGroup E (OppositeCoordinates.CM.coordinates E L.coordinates) →*
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)))
    (hρ : ∀ φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places), IsOpen {g | ρ g φ = φ})
    (hr : ρ.comp (SourceAdelic.ThetaRationalTheta.CM.rational E L) = WeilData.CM.finiteAction E L)
    {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q]) :
    (fun g : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] × FactorTheta.CM.RationalWeilFactorization.Away E L f =>
      FactorTheta.CM.action E L f g) =
    (fun g => ρ (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f g)) := by
  apply functions_of_active_and_rational
    (fun γ => RationalAwayTopology.CM.rational E L f γ)
    (RationalAwayTopology.CM.away_surjective E L f)
  · rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    exact FactorTheta.CM.action_mul E L f a₁ b₁ a₂ b₂
  · rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    exact native_mul E L ρ f a₁ b₁ a₂ b₂
  · intro γ
    apply LinearEquiv.ext
    intro φ
    exact rational_values E L ρ hr f γ φ
  · intro u
    apply LinearEquiv.ext
    intro φ
    exact active_values E L ρ hρ hr f u φ

theorem product_smooth (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
    {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
    (L : GeometricSource.CM.LinePeriod E B places d)
    (ρ : SourceFinite.Product.CM.FiniteGroup E (OppositeCoordinates.CM.coordinates E L.coordinates) →*
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)))
    (hρ : ∀ φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places), IsOpen {g | ρ g φ = φ})
    (hr : ρ.comp (SourceAdelic.ThetaRationalTheta.CM.rational E L) = WeilData.CM.finiteAction E L)
    {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    IsOpen {g : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] × FactorTheta.CM.RationalWeilFactorization.Away E L f |
      FactorTheta.CM.action E L f g φ = φ} := by
  exact smooth_of_function_eq
    (fun (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) φ => a φ)
    (fun g => ρ g) hρ
    (fun g => IntrinsicActiveClosure.CM.Intrinsic.assemble E L f g)
    (IntrinsicActiveClosure.CM.Intrinsic.continuous E L f)
    (fun g => FactorTheta.CM.action E L f g)
    (hom E L ρ hρ hr f) φ

theorem away_smooth (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
    {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
    (L : GeometricSource.CM.LinePeriod E B places d)
    (ρ : SourceFinite.Product.CM.FiniteGroup E (OppositeCoordinates.CM.coordinates E L.coordinates) →*
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)))
    (hρ : ∀ φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places), IsOpen {g | ρ g φ = φ})
    (hr : ρ.comp (SourceAdelic.ThetaRationalTheta.CM.rational E L) = WeilData.CM.finiteAction E L)
    {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    IsOpen {b : FactorTheta.CM.RationalWeilFactorization.Away E L f | FactorTheta.CM.action E L f (1, b) φ = φ} :=
  (product_smooth E L ρ hρ hr f φ).preimage (continuous_const.prodMk continuous_id)

end CM

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FactorSmoothness
