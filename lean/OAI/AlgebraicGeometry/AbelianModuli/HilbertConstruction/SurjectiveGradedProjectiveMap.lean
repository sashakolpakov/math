import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Surjective Graded Projective Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SurjectiveGradedProjectiveMap

noncomputable section

/-! A surjective graded ring map is surjective in every homogeneous
degree and induces a closed immersion of projective spectra. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization
open scoped Classical
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable (g : ℕ → Submodule R A) (h : ℕ → Submodule R B) [GradedAlgebra g] [GradedAlgebra h]
variable (f : g →+*ᵍ h) (hf : Function.Surjective f)

include hf

theorem surjectiveGradedMap_homogeneous_lift {d : ℕ} {b : B} (hb : b ∈ h d) :
    ∃ a : A, a ∈ g d ∧ f a = b := by
  obtain ⟨a, ha⟩ := hf b
  refine ⟨(DirectSum.decompose g a d).val, (DirectSum.decompose g a d).property, ?_⟩
  rw [f.map_directSumDecompose, ha, DirectSum.decompose_of_mem_same h hb]

theorem surjectiveGradedMap_irrelevant :
    HomogeneousIdeal.irrelevant h ≤ (HomogeneousIdeal.irrelevant g).map f := by
  apply (HomogeneousIdeal.irrelevant_le h).mpr
  intro d hd b hb
  obtain ⟨a, ha, rfl⟩ := surjectiveGradedMap_homogeneous_lift g h f hf hb
  exact Ideal.mem_map_of_mem f.toRingHom (HomogeneousIdeal.mem_irrelevant_of_mem g hd ha)

theorem surjectiveGradedMap_away_surjective {d : ℕ} (s : A) (hs : s ∈ g d) :
    Function.Surjective (HomogeneousLocalization.Away.map f s) := by
  intro z
  obtain ⟨k, b, hb, rfl⟩ := HomogeneousLocalization.Away.mk_surjective h (f.map_mem hs) z
  obtain ⟨a, ha, rfl⟩ := surjectiveGradedMap_homogeneous_lift g h f hf hb
  refine ⟨HomogeneousLocalization.Away.mk g hs k a ha, ?_⟩
  rw [HomogeneousLocalization.Away.map_mk]

theorem surjectiveGradedMap_restrict_closed {d : ℕ} (hd : 0 < d) (s : A) (hs : s ∈ g d) :
    IsClosedImmersion (Proj.map f (surjectiveGradedMap_irrelevant g h f hf) ∣_ Proj.basicOpen g s) := by
  let src := Proj.basicOpenIsoSpec h (f s) (f.map_mem hs) hd
  let tgt := Proj.basicOpenIsoSpec g s hs hd
  let a := Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map f s))
  have ha : IsClosedImmersion a := IsClosedImmersion.spec_of_surjective _
    (surjectiveGradedMap_away_surjective g h f hf s hs)
  have hdiag : src.inv ≫ (Proj.map f (surjectiveGradedMap_irrelevant g h f hf) ∣_ Proj.basicOpen g s) =
      a ≫ tgt.inv := by
    apply (cancel_mono (Proj.basicOpen g s).ι).mp
    erw [Category.assoc, morphismRestrict_ι]
    exact Proj.awayι_comp_map f (surjectiveGradedMap_irrelevant g h f hf) hd s hs
  apply (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) src.inv _).mp
  rw [hdiag]
  exact IsClosedImmersion.comp a tgt.inv

theorem surjectiveGradedMap_closed :
    IsClosedImmersion (Proj.map f (surjectiveGradedMap_irrelevant g h f hf)) := by
  let Index := Σ d : PNat, g d
  let U (s : Index) := Proj.basicOpen g s.2.val
  have hcover : iSup U = ⊤ := by
    apply Proj.iSup_basicOpen_eq_top
    apply (HomogeneousIdeal.toIdeal_irrelevant_le g).mpr
    intro d hd a ha
    exact Ideal.subset_span ⟨(⟨⟨d, hd⟩, ⟨a, ha⟩⟩ : Index), rfl⟩
  apply (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) U hcover).mpr
  intro s
  exact surjectiveGradedMap_restrict_closed g h f hf s.1.property s.2.val s.2.property

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SurjectiveGradedProjectiveMap
