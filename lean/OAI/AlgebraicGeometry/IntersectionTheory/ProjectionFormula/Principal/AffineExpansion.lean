import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SimultaneousAffineEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalBaseChange
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalWeight

/-! # Affine Expansion -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.AffineExpansion

noncomputable section

section

/-! After meeting fixed affine strata properly, intersecting a
principal quotient uses the actual divisor orders and native support
stalks, with no unspecified cycle or multiplicity data. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportStalk

def Expansion (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    {R : Type} [CommRing R] [IsNoetherianRing R] (j : Spec (.of R) ⟶ V.carrier)
    (v : PrimeSpectrum R) (r : R) (F : Finset (PrimeSpectrum R))
    (a : V.RationalDimensionCycle p) : Prop :=
  ∀ A ∈ a.support, ∀ C : V.DimensionCycleSupport (p + q), ∀ x : PrimeSpectrum R,
    j x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val → CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set V.carrier) →
    ∀ hvx : v.asIdeal ≤ x.asIdeal,
    letI : Algebra R ((Spec (.of R)).presheaf.stalk x) := (StructureSheaf.toStalk R x).hom.toAlgebra
    ∀ (N : ModuleCat ((Spec (.of R)).presheaf.stalk x)) [Module.Finite ((Spec (.of R)).presheaf.stalk x) N]
      (d : ℕ) [HasProjectiveDimensionLE N d],
      Module.support ((Spec (.of R)).presheaf.stalk x)
          (QuotSMulTop (StructureSheaf.toStalk R x r)
            (CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) (Affine.SupportStalk.support R v) x (Affine.SupportStalk.mem R v x hvx))) ∩
        Module.support ((Spec (.of R)).presheaf.stalk x) N ⊆
          {IsLocalRing.closedPoint ((Spec (.of R)).presheaf.stalk x)} →
      Tor.Euler.euler ((Spec (.of R)).presheaf.stalk x)
        (.of _ (QuotSMulTop (StructureSheaf.toStalk R x r)
          (CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) (Affine.SupportStalk.support R v) x (Affine.SupportStalk.mem R v x hvx)))) N d =
      ∑ z ∈ F, Affine.PrincipalWeight.weight R v r z *
        Tor.Euler.euler ((Spec (.of R)).presheaf.stalk x)
          ((Flat.Extension.baseChange R ((Spec (.of R)).presheaf.stalk x)).obj
            (.of R (R ⧸ z.asIdeal))) N d

theorem of_expansion (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    {R : Type} [CommRing R] [IsNoetherianRing R]
    (j : Spec (.of R) ⟶ V.carrier) (v : PrimeSpectrum R) (r : R) (hr : r ∉ v.asIdeal)
    (F : Finset (PrimeSpectrum R)) (a : V.RationalDimensionCycle p)
    (hF : ∀ z ∈ F, z ∈ Module.support R (QuotSMulTop r (R ⧸ v.asIdeal)))
    (he : SimultaneousAffineEuler.Expansion V p q j (.of R (QuotSMulTop r (R ⧸ v.asIdeal))) F a) :
    Expansion V p q j v r F a := by
  intro A hA C x hx hAC hvx
  let : Algebra R ((Spec (.of R)).presheaf.stalk x) := (StructureSheaf.toStalk R x).hom.toAlgebra
  intro N _ d _ hisolated
  have hs := (Affine.PrincipalBaseChange.equiv R v x hvx r).support_eq
  have hiso : Module.support ((Spec (.of R)).presheaf.stalk x)
      ((Flat.Extension.baseChange R ((Spec (.of R)).presheaf.stalk x)).obj
        (.of R (QuotSMulTop r (R ⧸ v.asIdeal)))) ∩
      Module.support ((Spec (.of R)).presheaf.stalk x) N ⊆
        {IsLocalRing.closedPoint ((Spec (.of R)).presheaf.stalk x)} := by
    rwa [hs]
  rw [← Affine.PrincipalBaseChange.euler R v x hvx r N d, he A hA C x hx hAC N d hiso]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Affine.PrincipalWeight.eq_length R v r hr z (hF z hz)]

end

/-! One move gives the native divisor-order expansion for finitely
many actual principal equations on integral affine supports. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Simultaneous

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FiltrationAvoidance

theorem exists_moved (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p : ℕ)
    [SmoothOfRelativeDimension m V.structureMap]
    {τ ι : Type} [Finite τ] [Finite ι]
    (R : τ → Type) [∀ i, CommRing (R i)] [∀ i, IsNoetherianRing (R i)]
    (j : ∀ i, Spec (.of (R i)) ⟶ V.carrier) [∀ i, IsOpenImmersion (j i)]
    (k : τ → ℕ) (v : ∀ i, PrimeSpectrum (R i))
    (hv : ∀ i, V.supportCodimension (Affine.FiltrationAvoidance.support (j i) (v i)) = k i)
    (r : ∀ i, R i) (hr : ∀ i, r i ∉ (v i).asIdeal)
    (Z₀ : ι → IrreducibleCloseds V.carrier) (a : V.RationalDimensionCycle p) :
    ∃ (F : ∀ i, Finset (PrimeSpectrum (R i))) (a' : V.RationalDimensionCycle p),
      CycleClass.Thom.IntersectionGeometry.RationallyEquivalent V p a a' ∧
      a' ∈ Proper.SupportCycles.submodule V p Z₀ ∧
      (∀ i, ∀ z ∈ F i, (v i).asIdeal ≤ z.asIdeal ∧ r i ∈ z.asIdeal ∧
        V.supportCodimension (Affine.FiltrationAvoidance.support (j i) z) = k i + 1) ∧
      (∀ i, ∀ z : PrimeSpectrum (R i), V.supportCodimension (Affine.FiltrationAvoidance.support (j i) z) = k i + 1 → z ∉ F i →
        Affine.PrincipalWeight.weight (R i) (v i) (r i) z = 0) ∧
      ∀ i, Expansion V p (k i + 1) (j i) (v i) (r i) (F i) a' := by
  let M := fun i => ModuleCat.of (R i) (QuotSMulTop (r i) (R i ⧸ (v i).asIdeal))
  have hM (i : τ) : ∀ z ∈ Module.support (R i) (M i),
      k i + 1 ≤ V.supportCodimension (Affine.FiltrationAvoidance.support (j i) z) :=
    Affine.PrincipalCodimension.bound V m (k i) (j i) (v i) (hv i) (r i) (hr i)
  obtain ⟨F, a', ha', hproper, hF, hout, he⟩ :=
    SimultaneousAffineEuler.exists_moved V m p R j (fun i => k i + 1) M hM Z₀ a
  refine ⟨F, a', ha', hproper, ?_, ?_, ?_⟩
  · intro i z hz
    have h := Affine.PrincipalCodimension.mem_support (v i) z (r i) (hF i z hz).1
    exact ⟨h.1, h.2, (hF i z hz).2.1⟩
  · intro i z hz hnot
    rw [Affine.PrincipalWeight.eq_length_all (R i) (v i) (r i) (hr i) z, hout i z hz hnot]
    rfl
  · intro i
    exact of_expansion V p (k i + 1) (j i) (v i) (r i) (hr i)
      (F i) a' (fun z hz => (hF i z hz).1) (he i)

end Simultaneous

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.AffineExpansion
