import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Euler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.FiniteLength
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Truncation

/-! # Isolated Tor Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsolatedTorEuler

noncomputable section

/-! At an isolated support intersection, finiteness for every term of a
short exact sequence follows from the middle module. Smooth stalk bounds
then give additivity of the exact local intersection formula. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem additivity (R : Type u) [CommRing R] [IsNoetherianRing R]
    (N : ModuleCat.{u} R) (S : ShortComplex (ModuleCat R)) (hS : S.ShortExact)
    [Module.Finite R S.X₂] [Module.Finite R N] (d : ℕ) [HasProjectiveDimensionLE N d]
    (p : PrimeSpectrum R) (hp : Module.support R S.X₂ ∩ Module.support R N ⊆ {p}) :
    Tor.Euler.euler R S.X₂ N d =
      Tor.Euler.euler R S.X₁ N d + Tor.Euler.euler R S.X₃ N d := by
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  have hf := (ModuleCat.mono_iff_injective S.f).mp inferInstance
  have hg := (ModuleCat.epi_iff_surjective S.g).mp inferInstance
  let : Module.Finite R S.X₁ := Module.Finite.of_injective S.f.hom hf
  let : Module.Finite R S.X₃ := Module.Finite.of_surjective S.g.hom hg
  have hp₁ : Module.support R S.X₁ ∩ Module.support R N ⊆ {p} :=
    (Set.inter_subset_inter_left _ (Module.support_subset_of_injective S.f.hom hf)).trans hp
  have hp₃ : Module.support R S.X₃ ∩ Module.support R N ⊆ {p} :=
    (Set.inter_subset_inter_left _ (Module.support_subset_of_surjective S.g.hom hg)).trans hp
  exact Tor.Euler.additivity R N S hS d
    (Tor.FiniteLength.tor_length_ne_top R S.X₁ N p hp₁)
    (Tor.FiniteLength.tor_length_ne_top R S.X₂ N p hp)
    (Tor.FiniteLength.tor_length_ne_top R S.X₃ N p hp₃)
    (BoundedResolution.tor_isZero R S.X₃ N d (d + 1) (by omega))

def submoduleSequence (R : Type u) [CommRing R] (M : ModuleCat.{u} R) (L : Submodule R M) :
    ShortComplex (ModuleCat R) :=
  ShortComplex.mk (ModuleCat.ofHom L.subtype) (ModuleCat.ofHom L.mkQ)
    (ModuleCat.hom_ext (by ext; simp))

theorem submoduleSequence_shortExact (R : Type u) [CommRing R]
    (M : ModuleCat.{u} R) (L : Submodule R M) : (submoduleSequence R M L).ShortExact := by
  exact
    { mono_f := (ModuleCat.mono_iff_injective (ModuleCat.ofHom L.subtype)).mpr L.subtype_injective
      exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (submoduleSequence R M L)).mpr (LinearMap.exact_subtype_mkQ L)
      epi_g := (ModuleCat.epi_iff_surjective (ModuleCat.ofHom L.mkQ)).mpr L.mkQ_surjective }

theorem intersectionMultiplicity_eq_submodule_sum
    (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m d : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (A B : IrreducibleCloseds X.carrier)
    (hproper : ∀ D : IrreducibleCloseds X.carrier,
      (D : Set X.carrier) ⊆ (A : Set X.carrier) ∩ B → d ≤ X.supportCodimension D)
    (C : X.DimensionCycleSupport d)
    (hxA : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A : Set X.carrier))
    (hxB : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (B : Set X.carrier))
    (L : Submodule (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))
      (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier A (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA)) :
    CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A B C.val =
      Tor.Euler.euler _ (.of _ L) (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier B (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxB) m +
      Tor.Euler.euler _ (.of _ ((CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier A (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA) ⧸ L))
        (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier B (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxB) m := by
  let R := X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
  let M := CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier A (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA
  let N := CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier B (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxB
  let : Module.Finite R M := Local.TorFinite.localSupportModule_finite _ _ _ _
  let : Module.Finite R N := Local.TorFinite.localSupportModule_finite _ _ _ _
  let : Module.Finite R (submoduleSequence R M L).X₂ :=
    (inferInstance : Module.Finite R M)
  let : HasProjectiveDimensionLE N m :=
    Smooth.StalkDimension.stalk_bound X.structureMap m (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) N
  rw [Truncation.intersectionMultiplicity_eq_relative_sum X m A B C.val hxA hxB]
  exact additivity R N (submoduleSequence R M L) (submoduleSequence_shortExact R M L) m
    (IsLocalRing.closedPoint R)
    (Proper.TorLength.local_support_intersection_subset X m d A B hproper C hxA hxB)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsolatedTorEuler
