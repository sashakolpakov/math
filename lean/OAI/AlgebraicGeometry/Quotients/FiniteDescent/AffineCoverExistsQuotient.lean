import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Chart
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineQuotientOf
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RelationRestrictionOn

/-! # Affine Cover Exists Quotient -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineCoverExistsQuotient.Construction.AffineCoverQuotient

/-!
# Scheme quotients from invariant affine covers

For an equivalence relation with finite source, an invariant affine cover
with finite-free source restrictions suffices. The local spectra of invariant
rings, their transitions, and the global quotient are all constructed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

/-- Construct the scheme quotient from invariant affine charts on which the
source of the relation is free of finite rank. The input is geometric chart
data and module bases, with no local or global quotient assumed. -/
theorem exists_quotient
    {R X : Scheme.{u}} (s t : R ⟶ X) [IsFinite s]
    (e : CategoryTheory.EquivalenceRelation s t) (𝒰 : X.OpenCover)
    [Category.{v} 𝒰.I₀] [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] [𝒰.LocallyDirected]
    [∀ i, IsAffine (𝒰.X i)]
    (Rᵢ : 𝒰.I₀ → Scheme.{u}) (jR : ∀ i, Rᵢ i ⟶ R)
    (sᵢ tᵢ : ∀ i, Rᵢ i ⟶ 𝒰.X i)
    (hs : ∀ i, IsPullback (sᵢ i) (jR i) (𝒰.f i) s)
    (ht : ∀ i, tᵢ i ≫ 𝒰.f i = jR i ≫ t)
    (n : 𝒰.I₀ → ℕ)
    (b : ∀ i, letI := (sᵢ i).appTop.hom.toAlgebra;
      Module.Basis (Fin (n i)) Γ(𝒰.X i, ⊤) Γ(Rᵢ i, ⊤)) :
    ∃ (Q : Scheme.{u}) (π : X ⟶ Q),
      IsFinite π ∧ Flat π ∧ LocallyOfFinitePresentation π ∧ Surjective π ∧
      IsKernelPair π s t ∧
      ∀ (T : Scheme.{u}) (f : X ⟶ T), s ≫ f = t ≫ f →
        ∃! g : Q ⟶ T, π ≫ g = f := by
  let : ∀ i, IsFinite (sᵢ i) := fun i =>
    MorphismProperty.of_isPullback (hs i).flip inferInstance
  let : ∀ i, IsAffine (Rᵢ i) := fun i => isAffine_of_isAffineHom (sᵢ i)
  let eᵢ (i : 𝒰.I₀) := RelationRestrictionOn.Construction.RelationRestriction.equivalenceRelation e
    (𝒰.f i) (jR i) (sᵢ i) (tᵢ i) (hs i) (ht i)
  have hp (i : 𝒰.I₀) := AffineQuotientOf.Construction.AffineQuotient.projection_properties_of_finiteFree_absolute
    (sᵢ i) (tᵢ i) (eᵢ i) (b i)
  let d : Chart.Construction.ChartQuotients.Data s t 𝒰 :=
    { quotient := fun i => AffineRing.Construction.Affine.quotient (sᵢ i).appTop.hom (tᵢ i).appTop.hom
      projection := fun i => AffineQuotientOf.Construction.AffineQuotient.projection (sᵢ i) (tᵢ i)
      finite := fun i => (hp i).1
      flat := fun i => (hp i).2.1
      finitelyPresented := fun i => (hp i).2.2.1
      surjective := fun i => (hp i).2.2.2.1
      relation := Rᵢ
      inclusion := jR
      source := sᵢ
      target := tᵢ
      source_isPullback := hs
      target_comp := ht
      kernelPair := fun i => (hp i).2.2.2.2 }
  exact d.exists_quotient

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineCoverExistsQuotient.Construction.AffineCoverQuotient
