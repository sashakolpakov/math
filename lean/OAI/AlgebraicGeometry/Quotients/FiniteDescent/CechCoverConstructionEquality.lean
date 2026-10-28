import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleCechPullbackShort
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechShort

/-! # Cech Cover Construction Equality -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechCoverConstructionEquality.Construction.CechCoverEquality

noncomputable section

/-! Equal open covers give canonically identified Cech complexes, compatibly
with the geometric restriction maps. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

def iso {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) {ι : Type u}
    {U V : ι → X.Opens} (h : U = V) :
    CechShort.Construction.CechShortCoordinates.target π M U ≅ CechShort.Construction.CechShortCoordinates.target π M V :=
  eqToIso (congrArg (fun W => CechShort.Construction.CechShortCoordinates.target π M W) h)

variable {X Y S : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ S)
variable (hf : f ≫ π = ρ) (M : X.Modules) {ι κ : Type u}

theorem source {U₀ U₁ : ι → X.Opens} (h : U₀ = U₁) (V : κ → Y.Opens) (r : κ → ι)
    (h₀ : ∀ a, V a ≤ f ⁻¹ᵁ U₀ (r a)) (h₁ : ∀ a, V a ≤ f ⁻¹ᵁ U₁ (r a)) :
    (iso π M h).hom ≫ ModuleCechPullbackShort.Construction.ModuleCechPullback.shortMap f π ρ hf M U₁ V r h₁ =
      ModuleCechPullbackShort.Construction.ModuleCechPullback.shortMap f π ρ hf M U₀ V r h₀ := by
  subst U₁
  exact Category.id_comp _

theorem target (U : ι → X.Opens) {V₀ V₁ : κ → Y.Opens} (h : V₀ = V₁) (r : κ → ι)
    (h₀ : ∀ a, V₀ a ≤ f ⁻¹ᵁ U (r a)) (h₁ : ∀ a, V₁ a ≤ f ⁻¹ᵁ U (r a)) :
    ModuleCechPullbackShort.Construction.ModuleCechPullback.shortMap f π ρ hf M U V₀ r h₀ ≫
        (iso ρ ((Scheme.Modules.pullback f).obj M) h).hom =
      ModuleCechPullbackShort.Construction.ModuleCechPullback.shortMap f π ρ hf M U V₁ r h₁ := by
  subst V₁
  exact Category.comp_id _

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechCoverConstructionEquality.Construction.CechCoverEquality
