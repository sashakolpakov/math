import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResolutionAugment
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Flat
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension

/-! # Bounded Resolution -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BoundedResolution

noncomputable section

/-! A projective-dimension bound yields an actual resolution that vanishes
above that bound. Computing the native left-derived functor on this
resolution proves its higher vanishing, in particular for Tor. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory

universe u v w

variable (R : Type u) [CommRing R]

theorem exists_bounded_resolution (M : ModuleCat.{u} R) (d : ℕ)
    [HasProjectiveDimensionLE M d] :
    ∃ P : ProjectiveResolution M, ∀ n, d < n → IsZero (P.complex.X n) := by
  induction d generalizing M with
  | zero =>
    let : Projective M := (projective_iff_hasProjectiveDimensionLE_zero M).mpr inferInstance
    refine ⟨ProjectiveResolution.self M, ?_⟩
    intro n hn
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  | succ d ih =>
    let S := M.projectiveShortComplex
    have hS := M.shortExact_projectiveShortComplex
    let : HasProjectiveDimensionLE S.X₁ d :=
      (hS.hasProjectiveDimensionLT_X₃_iff d inferInstance).mp inferInstance
    obtain ⟨Q, hQ⟩ := ih S.X₁
    refine ⟨ResolutionAugment.resolution S hS Q, ?_⟩
    intro n hn
    cases n with
    | zero => omega
    | succ n => exact hQ n (by omega)

theorem leftDerived_isZero {C : Type w} [Category.{v} C] [Abelian C]
    (F : ModuleCat.{u} R ⥤ C) [F.Additive] (M : ModuleCat R) (d n : ℕ)
    [HasProjectiveDimensionLE M d] (hn : d < n) :
    IsZero ((F.leftDerived n).obj M) := by
  obtain ⟨P, hP⟩ := exists_bounded_resolution R M d
  apply IsZero.of_iso _ (P.isoLeftDerivedObj F n)
  change IsZero (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homology n)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact HomologicalComplex.ExactAt.of_isZero (F.map_isZero (hP n hn))

theorem tor_isZero (M N : ModuleCat.{u} R) (d n : ℕ)
    [HasProjectiveDimensionLE N d] (hn : d < n) :
    IsZero (((Tor (ModuleCat R) n).obj M).obj N) :=
  leftDerived_isZero R (tensorLeft M) N d n hn

theorem tor_length_zero (M N : ModuleCat.{u} R) (d n : ℕ)
    [HasProjectiveDimensionLE N d] (hn : d < n) :
    Module.length R (((Tor (ModuleCat R) n).obj M).obj N) = 0 := by
  let := ModuleCat.subsingleton_of_isZero (tor_isZero R M N d n hn)
  exact Module.length_eq_zero

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BoundedResolution
