import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.AffinePullback
import Mathlib.RingTheory.Nilpotent.Lemmas

/-! # Nilpotent Fiber Ampleness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentFiberAmpleness

noncomputable section

/-! Ampleness on a closed nilpotent field reduction gives ampleness on
all field fibers, and a projective presentation for a proper flat family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {R k : Type u} [CommRing R] [CommRing k]
  (ρ : R →+* k) (hρ : Function.Surjective ρ)
  (hker : ∀ a ∈ RingHom.ker ρ, IsNilpotent a)

include hρ hker in
theorem field_factor {K : Type u} [Field K] (b : Spec (.of K) ⟶ Spec (.of R)) :
    ∃ c : Spec (.of K) ⟶ Spec (.of k), c ≫ Spec.map (CommRingCat.ofHom ρ) = b := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective b
  have h : RingHom.ker ρ ≤ RingHom.ker φ.hom := by
    intro a ha
    exact (hker a ha).map φ.hom |>.eq_zero
  let ψ := ρ.liftOfSurjective hρ ⟨φ.hom, h⟩
  refine ⟨Spec.map (CommRingCat.ofHom ψ), ?_⟩
  rw [← Spec.map_comp]
  exact congrArg (fun f : R →+* K => Spec.map (CommRingCat.ofHom f))
    (ρ.liftOfSurjective_comp hρ ⟨φ.hom, h⟩)

include hρ hker in
theorem reduction_surjective : Surjective (Spec.map (CommRingCat.ofHom ρ)) := by
  constructor
  change Function.Surjective (PrimeSpectrum.comap ρ)
  rw [← Set.range_eq_univ, range_comap_of_surjective _ _ hρ]
  apply Set.eq_univ_of_forall
  intro x a ha
  exact (nilpotent_iff_mem_prime.mp (hker a ha)) x.asIdeal x.isPrime

variable {X Y : Scheme.{u}} (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of k))
  (i : Y ⟶ X) (hp : IsPullback i g f (Spec.map (CommRingCat.ofHom ρ)))
  (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : (L.pullback i).IsAmple)

include hρ hker hp hL in
theorem field_ample {K : Type u} [Field K] (b : Spec (.of K) ⟶ Spec (.of R)) :
    (L.pullback (pullback.fst f b)).IsAmple := by
  obtain ⟨c, hc⟩ := field_factor ρ hρ hker b
  have hs := (IsPullback.of_hasPullback g c).paste_horiz hp
  rw [hc] at hs
  let e := hs.isoPullback
  let : IsAffineHom c := inferInstance
  let : IsAffineHom (pullback.fst g c) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback g c).flip inferInstance
  have ha := hL.pullback_of_isAffineHom (pullback.fst g c)
  have hb := ha.pullback_of_isAffineHom e.inv
  apply hb.of_iso
  exact (Scheme.Modules.pullbackComp e.inv (pullback.fst g c)).app (L.pullback i).sheaf ≪≫
    (Scheme.Modules.pullbackComp (e.inv ≫ pullback.fst g c) i).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr (by
        rw [Category.assoc]
        exact hs.isoPullback_inv_fst)).app L.sheaf

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentFiberAmpleness
