import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-! # Connective Derived Is -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ConnectiveDerivedIs.ConnectiveDerivedMaps

noncomputable section

/-! Maps from a complex concentrated in its lowest degree into a connective complex are already actual cochain maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {X Y : CochainComplex C ℤ}

theorem concentrated_isIso (n : ℤ) [X.IsStrictlyGE n] [X.IsStrictlyLE n]
    [Y.IsStrictlyGE n] [Y.IsStrictlyLE n] (s : X ⟶ Y) [IsIso (DerivedCategory.Q.map s)] :
    IsIso s := by
  obtain ⟨A, hA⟩ := X.exists_iso_single n
  obtain ⟨B, hB⟩ := Y.exists_iso_single n
  obtain ⟨eX⟩ : Nonempty (X ≅ (CochainComplex.singleFunctor C n).obj A) := hA
  obtain ⟨eY⟩ : Nonempty (Y ≅ (CochainComplex.singleFunctor C n).obj B) := hB
  obtain ⟨a, ha⟩ := (CochainComplex.singleFunctor C n).map_surjective (eX.inv ≫ s ≫ eY.hom)
  have : IsIso ((DerivedCategory.singleFunctor C n).map a) := by
    change IsIso (DerivedCategory.Q.map ((CochainComplex.singleFunctor C n).map a))
    rw [ha, Functor.map_comp, Functor.map_comp]
    infer_instance
  have : IsIso a := isIso_of_reflects_iso a (DerivedCategory.singleFunctor C n)
  have : IsIso (eX.inv ≫ s ≫ eY.hom) := by rw [← ha]; infer_instance
  have : IsIso (s ≫ eY.hom) := IsIso.of_isIso_comp_left eX.inv (s ≫ eY.hom)
  exact IsIso.of_isIso_comp_right s eY.hom

theorem surjective (n : ℤ) [X.IsStrictlyGE n] [X.IsStrictlyLE n] [Y.IsStrictlyGE n] :
    Function.Surjective (DerivedCategory.Q.map : (X ⟶ Y) → _) := by
  intro f
  obtain ⟨Z, _, _, s, _, g, hf⟩ :=
    DerivedCategory.right_fac_of_isStrictlyLE_of_isStrictlyGE n n f
  have : IsIso s := concentrated_isIso n s
  exact ⟨inv s ≫ g, by simp only [Functor.map_comp, Functor.map_inv, hf]⟩

omit [HasDerivedCategory.{w} C] in
theorem homology_injective (n : ℤ) [X.IsStrictlyGE n] [X.IsStrictlyLE n] [Y.IsStrictlyGE n] :
    Function.Injective (fun f : X ⟶ Y => HomologicalComplex.homologyMap f n) := by
  have : IsIso (X.iCycles n) := X.isIso_iCycles n (n + 1) (by simp)
    ((X.isZero_of_isStrictlyLE n (n + 1) (by omega)).eq_of_tgt _ _)
  have : IsIso (Y.homologyπ n) := Y.isIso_homologyπ (n - 1) n (by simp)
    ((Y.isZero_of_isStrictlyGE n (n - 1) (by omega)).eq_of_src _ _)
  intro f g h
  dsimp only at h
  have hc : HomologicalComplex.cyclesMap f n = HomologicalComplex.cyclesMap g n := by
    rw [← cancel_mono (Y.homologyπ n), ← HomologicalComplex.homologyπ_naturality,
      ← HomologicalComplex.homologyπ_naturality, h]
  apply HomologicalComplex.Hom.ext
  funext i
  rcases lt_trichotomy i n with hi | hi | hi
  · exact (X.isZero_of_isStrictlyGE n i hi).eq_of_src _ _
  · subst i
    rw [← cancel_epi (X.iCycles n), ← HomologicalComplex.cyclesMap_i,
      ← HomologicalComplex.cyclesMap_i, hc]
  · exact (X.isZero_of_isStrictlyLE n i hi).eq_of_src _ _

theorem injective (n : ℤ) [X.IsStrictlyGE n] [X.IsStrictlyLE n] [Y.IsStrictlyGE n] :
    Function.Injective (DerivedCategory.Q.map : (X ⟶ Y) → _) := by
  intro f g h
  apply homology_injective n
  have hf := NatIso.naturality_1 (DerivedCategory.homologyFunctorFactors C n) f
  have hg := NatIso.naturality_1 (DerivedCategory.homologyFunctorFactors C n) g
  change (HomologicalComplex.homologyFunctor C (.up ℤ) n).map f =
    (HomologicalComplex.homologyFunctor C (.up ℤ) n).map g
  rw [← hf, ← hg]
  simp only [Functor.comp_map, h]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ConnectiveDerivedIs.ConnectiveDerivedMaps
