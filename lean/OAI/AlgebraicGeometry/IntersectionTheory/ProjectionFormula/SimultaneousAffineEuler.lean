import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.EulerStrata

/-! # Simultaneous Affine Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SimultaneousAffineEuler

noncomputable section

/-! A single cycle move works for finitely many modules on different
affine charts, and for any additional finite collection of supports.
Each Euler expansion retains its own native generic lengths. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FiltrationAvoidance

def Expansion (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    {R : Type} [CommRing R] (j : Spec (.of R) ⟶ V.carrier)
    (M : ModuleCat R) (F : Finset (PrimeSpectrum R)) (a : V.RationalDimensionCycle p) : Prop :=
  ∀ A ∈ a.support, ∀ C : V.DimensionCycleSupport (p + q), ∀ x : PrimeSpectrum R,
    j x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val → CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set V.carrier) →
    letI : Algebra R ((Spec (.of R)).presheaf.stalk x) := (StructureSheaf.toStalk R x).hom.toAlgebra
    ∀ (N : ModuleCat ((Spec (.of R)).presheaf.stalk x)) [Module.Finite ((Spec (.of R)).presheaf.stalk x) N]
      (d : ℕ) [HasProjectiveDimensionLE N d],
      Module.support ((Spec (.of R)).presheaf.stalk x)
          ((Flat.Extension.baseChange R ((Spec (.of R)).presheaf.stalk x)).obj M) ∩
        Module.support ((Spec (.of R)).presheaf.stalk x) N ⊆
          {IsLocalRing.closedPoint ((Spec (.of R)).presheaf.stalk x)} →
      Tor.Euler.euler ((Spec (.of R)).presheaf.stalk x)
        ((Flat.Extension.baseChange R ((Spec (.of R)).presheaf.stalk x)).obj M) N d =
      ∑ z ∈ F, ((FiltrationBaseLength.length R (Localization.AtPrime z.asIdeal) M).toNat : ℚ) *
        Tor.Euler.euler ((Spec (.of R)).presheaf.stalk x)
          ((Flat.Extension.baseChange R ((Spec (.of R)).presheaf.stalk x)).obj
            (.of R (R ⧸ z.asIdeal))) N d

theorem exists_moved (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p : ℕ)
    [SmoothOfRelativeDimension m V.structureMap]
    {τ ι : Type} [Finite τ] [Finite ι]
    (R : τ → Type) [∀ i, CommRing (R i)] [∀ i, IsNoetherianRing (R i)]
    (j : ∀ i, Spec (.of (R i)) ⟶ V.carrier) [∀ i, IsOpenImmersion (j i)]
    (q : τ → ℕ) (M : ∀ i, ModuleCat (R i)) [∀ i, Module.Finite (R i) (M i)]
    (hM : ∀ i, ∀ v ∈ Module.support (R i) (M i), q i ≤ V.supportCodimension (Affine.FiltrationAvoidance.support (j i) v))
    (Z₀ : ι → IrreducibleCloseds V.carrier) (a : V.RationalDimensionCycle p) :
    ∃ (F : ∀ i, Finset (PrimeSpectrum (R i))) (a' : V.RationalDimensionCycle p),
      CycleClass.Thom.IntersectionGeometry.RationallyEquivalent V p a a' ∧
      a' ∈ Proper.SupportCycles.submodule V p Z₀ ∧
      (∀ i, ∀ z ∈ F i, z ∈ Module.support (R i) (M i) ∧
        V.supportCodimension (Affine.FiltrationAvoidance.support (j i) z) = q i ∧
        FiltrationBaseLength.length (R i) (Localization.AtPrime z.asIdeal) (M i) ≠ ⊤) ∧
      (∀ i, ∀ z : PrimeSpectrum (R i), V.supportCodimension (Affine.FiltrationAvoidance.support (j i) z) = q i → z ∉ F i →
        FiltrationBaseLength.length (R i) (Localization.AtPrime z.asIdeal) (M i) = 0) ∧
      ∀ i, Expansion V p (q i) (j i) (M i) (F i) a' := by
  classical
  choose F Z hZ hF hout he using
    fun i => Affine.EulerStrata.exists_data (R i) V m (q i) (j i) (M i) (hM i)
  let I := ι ⊕ (Σ i, Z i)
  let family : I → IrreducibleCloseds V.carrier := Sum.elim Z₀ (fun z => z.2.val)
  obtain ⟨a', ha', hp⟩ := General.ChowMoving.cycle V m family p a
  refine ⟨F, a', ha', ?_, hF, hout, ?_⟩
  · intro i A hA
    exact hp (.inl i) A hA
  · intro i
    apply he i p a'
    intro B A hA
    exact hp (.inr ⟨i, B⟩) A hA

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SimultaneousAffineEuler
