import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.HigherAvoidance
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizedFixedFiltration

/-! # Filtration Avoidance -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FiltrationAvoidance

noncomputable section

/-! Moving against the closures of fixed affine filtration primes
removes higher-codimension factors from the actual local Tor computation.
The resulting modules vanish after native stalk localization. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {R : Type} [CommRing R] {X : Scheme} (j : Spec (.of R) ⟶ X)

def support (q : PrimeSpectrum R) : IrreducibleCloseds X :=
  irreducibleSetEquivPoints.symm (j q)

theorem mem (p q : PrimeSpectrum R) (hqp : q.asIdeal ≤ p.asIdeal) :
    j p ∈ (FiltrationAvoidance.support j q : Set X) := by
  have h : j q ⤳ j p := ((PrimeSpectrum.le_iff_specializes q p).mp hqp).map j.continuous
  exact h.mem_closed (FiltrationAvoidance.support j q).isClosed (subset_closure (Set.mem_singleton _))

theorem prime_not_le (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (j : Spec (.of R) ⟶ V.carrier)
    (p q : ℕ) (A : V.DimensionCycleSupport p) (C : V.DimensionCycleSupport (p + q))
    (x v : PrimeSpectrum R) (hx : j x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
    (hA : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set V.carrier))
    (hv : q < V.supportCodimension (FiltrationAvoidance.support j v))
    (hproper : ∀ D : IrreducibleCloseds V.carrier,
      (D : Set V.carrier) ⊆ (A.val : Set V.carrier) ∩ (FiltrationAvoidance.support j v : Set V.carrier) →
        p + V.supportCodimension (FiltrationAvoidance.support j v) ≤ V.supportCodimension D) :
    ¬ v.asIdeal ≤ x.asIdeal := by
  intro he
  have hm := mem j x v he
  rw [hx] at hm
  exact Support.HigherAvoidance.point_notMem V p q A (FiltrationAvoidance.support j v) hv hproper C ⟨hA, hm⟩

theorem native_euler_zero (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (j : Spec (.of R) ⟶ V.carrier)
    (p q : ℕ) (A : V.DimensionCycleSupport p) (C : V.DimensionCycleSupport (p + q))
    (x v : PrimeSpectrum R) (hx : j x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
    (hA : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set V.carrier))
    (hv : q < V.supportCodimension (FiltrationAvoidance.support j v))
    (hproper : ∀ D : IrreducibleCloseds V.carrier,
      (D : Set V.carrier) ⊆ (A.val : Set V.carrier) ∩ (FiltrationAvoidance.support j v : Set V.carrier) →
        p + V.supportCodimension (FiltrationAvoidance.support j v) ≤ V.supportCodimension D)
    (N : ModuleCat ((Spec (.of R)).presheaf.stalk x)) (d : ℕ) :
    letI : Algebra R ((Spec (.of R)).presheaf.stalk x) := (StructureSheaf.toStalk R x).hom.toAlgebra
    Tor.Euler.euler ((Spec (.of R)).presheaf.stalk x)
      ((Flat.Extension.baseChange R ((Spec (.of R)).presheaf.stalk x)).obj (.of R (R ⧸ v.asIdeal))) N d = 0 := by
  let : Algebra R ((Spec (.of R)).presheaf.stalk x) := (StructureSheaf.toStalk R x).hom.toAlgebra
  let : IsLocalization x.asIdeal.primeCompl ((Spec (.of R)).presheaf.stalk x) := by
    change IsLocalization x.asIdeal.primeCompl ((structurePresheafInCommRingCat R).stalk x)
    infer_instance
  exact LocalizedFixedFiltration.prime_euler_zero R ((Spec (.of R)).presheaf.stalk x) x v
    (prime_not_le V j p q A C x v hx hA hv hproper) N d

theorem move (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (j : Spec (.of R) ⟶ V.carrier) (m p q : ℕ)
    [SmoothOfRelativeDimension m V.structureMap] {τ : Type} [Finite τ]
    (v : τ → PrimeSpectrum R) (hv : ∀ i, q < V.supportCodimension (FiltrationAvoidance.support j (v i)))
    (a : V.RationalDimensionCycle p) :
    ∃ a' : V.RationalDimensionCycle p, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent V p a a' ∧
      ∀ i, ∀ A ∈ a'.support, ∀ C : V.DimensionCycleSupport (p + q), ∀ x : PrimeSpectrum R,
        j x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val → CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set V.carrier) →
          ¬ (v i).asIdeal ≤ x.asIdeal := by
  obtain ⟨a', ha', hp⟩ := General.ChowMoving.cycle V m (fun i => FiltrationAvoidance.support j (v i)) p a
  exact ⟨a', ha', fun i A hA C x hx hAC => prime_not_le V j p q A C x (v i) hx hAC (hv i) (hp i A hA)⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FiltrationAvoidance
