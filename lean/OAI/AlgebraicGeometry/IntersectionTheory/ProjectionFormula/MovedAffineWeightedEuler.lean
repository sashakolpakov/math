import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovedAffineFiltrationEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.MultiplicitySum

/-! # Moved Affine Weighted Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovedAffineWeightedEuler

noncomputable section

/-! After the permitted geometric move, local Tor Euler pairings
are the finite sum of the top-dimensional prime-support pairings,
weighted by the original module's actual finite generic lengths. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FiltrationAvoidance

theorem exists_moved (R : Type) [CommRing R] [IsNoetherianRing R]
    (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ) [SmoothOfRelativeDimension m V.structureMap]
    (j : Spec (.of R) ⟶ V.carrier) [IsOpenImmersion j]
    (M : ModuleCat R) [Module.Finite R M]
    (hM : ∀ v ∈ Module.support R M, q ≤ V.supportCodimension (Affine.FiltrationAvoidance.support j v))
    (a : V.RationalDimensionCycle p) :
    ∃ (F : Finset (PrimeSpectrum R)) (a' : V.RationalDimensionCycle p),
      CycleClass.Thom.IntersectionGeometry.RationallyEquivalent V p a a' ∧
      (∀ z ∈ F, V.supportCodimension (Affine.FiltrationAvoidance.support j z) = q ∧
        FiltrationBaseLength.length R (Localization.AtPrime z.asIdeal) M ≠ ⊤) ∧
      ∀ A ∈ a'.support, ∀ C : V.DimensionCycleSupport (p + q), ∀ x : PrimeSpectrum R,
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
                (.of R (R ⧸ z.asIdeal))) N d := by
  obtain ⟨k, v, a', ha', _, hcount, he⟩ := MovedAffineFiltrationEuler.exists_moved R V m p q j M hM a
  let P := fun z : PrimeSpectrum R => V.supportCodimension (Affine.FiltrationAvoidance.support j z) = q
  let F := (Finset.univ.image v).filter P
  refine ⟨F, a', ha', ?_, ?_⟩
  · intro z hz
    have hP := (Finset.mem_filter.mp hz).2
    refine ⟨hP, ?_⟩
    rw [hcount z hP]
    exact ENat.natCast_ne_top _
  · intro A hA C x hx hAC
    let : Algebra R ((Spec (.of R)).presheaf.stalk x) := (StructureSheaf.toStalk R x).hom.toAlgebra
    intro N _ d _ hisolated
    refine (he A hA C x hx hAC N d hisolated).trans ?_
    simpa only [P, F] using
      (ProjectionFormula.Finite.MultiplicitySum.reindex k v P
        (fun z => FiltrationBaseLength.length R (Localization.AtPrime z.asIdeal) M) hcount
        (fun z => Tor.Euler.euler ((Spec (.of R)).presheaf.stalk x)
          ((Flat.Extension.baseChange R ((Spec (.of R)).presheaf.stalk x)).obj
            (.of R (R ⧸ z.asIdeal))) N d))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovedAffineWeightedEuler
