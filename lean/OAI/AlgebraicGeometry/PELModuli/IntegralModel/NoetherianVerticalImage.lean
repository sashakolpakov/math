import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Topology.Sober

/-! # Noetherian Vertical Image -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.NoetherianVerticalImage

noncomputable section

section

/-! A noetherian scheme whose image misses the generic point of a
domain is supported over one nonzero equation on the base. The equation
is the product of witnesses at the finitely many component generic points. -/

open _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem noetherian_vertical_image_annihilator
    {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} [IsNoetherian X]
    (f : X ⟶ Spec (.of R)) (h : ∀ x : X, (f x).asIdeal ≠ ⊥) :
    ∃ r : R, r ≠ 0 ∧ ∀ x : X, r ∈ (f x).asIdeal := by
  classical
  let I := irreducibleComponents X
  have : Finite I := NoetherianSpace.finite_irreducibleComponents.to_subtype
  let : Fintype I := Fintype.ofFinite I
  let p (i : I) : X := i.property.1.genericPoint
  choose a ha hn using fun i : I => ((f (p i)).asIdeal.ne_bot_iff).mp (h (p i))
  refine ⟨∏ i, a i, Finset.prod_ne_zero_iff.mpr (fun i _ => hn i), ?_⟩
  intro x
  let i : I := ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  have hx : x ∈ i.val := mem_irreducibleComponent
  have hp : p i ⤳ x :=
    (i.property.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ i.property)).specializes hx
  have hf : (f (p i)).asIdeal ≤ (f x).asIdeal :=
    (PrimeSpectrum.le_iff_specializes _ _).mpr (hp.map f.continuous)
  exact (f x).asIdeal.mem_of_dvd (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) (hf (ha i))

end

section

/-! The finite generic-point argument for a vertical locus also applies
to noetherian sober closed subspaces, without choosing a closed scheme model. -/

open _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem noetherian_topological_vertical_annihilator
    {R : Type} [CommRing R] [IsDomain R]
    {X : Type} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X]
    (f : X → PrimeSpectrum R) (hf : Continuous f) (h : ∀ x : X, (f x).asIdeal ≠ ⊥) :
    ∃ r : R, r ≠ 0 ∧ ∀ x : X, r ∈ (f x).asIdeal := by
  classical
  let I := irreducibleComponents X
  have : Finite I := NoetherianSpace.finite_irreducibleComponents.to_subtype
  let : Fintype I := Fintype.ofFinite I
  let p (i : I) : X := i.property.1.genericPoint
  choose a ha hn using fun i : I => ((f (p i)).asIdeal.ne_bot_iff).mp (h (p i))
  refine ⟨∏ i, a i, Finset.prod_ne_zero_iff.mpr (fun i _ => hn i), ?_⟩
  intro x
  let i : I := ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  have hx : x ∈ i.val := mem_irreducibleComponent
  have hp : p i ⤳ x :=
    (i.property.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ i.property)).specializes hx
  have hi : (f (p i)).asIdeal ≤ (f x).asIdeal :=
    (PrimeSpectrum.le_iff_specializes _ _).mpr (hp.map hf)
  exact (f x).asIdeal.mem_of_dvd (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) (hi (ha i))

end

/-! An open containing the complete generic fiber contains every
fiber after inverting one nonzero coefficient. -/

open _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem noetherian_generic_open_locus_away
    {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (.of R)) (U : X.Opens)
    (hgeneric : ∀ x : X, (p x).asIdeal = ⊥ → x ∈ U) :
    ∃ r : R, r ≠ 0 ∧ ∀ x : X, r ∉ (p x).asIdeal → x ∈ U := by
  let C : Set X := (U : Set X)ᶜ
  have : QuasiSober C := U.isOpen.isClosed_compl.isClosedEmbedding_subtypeVal.quasiSober
  obtain ⟨r, hr, hC⟩ := noetherian_topological_vertical_annihilator
    (fun x : C => p x.val) (p.continuous.comp continuous_subtype_val)
    (fun x hx => x.property (hgeneric x.val hx))
  refine ⟨r, hr, fun x hx => ?_⟩
  by_contra hn
  exact hx (hC ⟨x, hn⟩)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.NoetherianVerticalImage
