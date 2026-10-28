import OAI.ArithmeticGeometry.Models.SpreadingOut.SchemeFiberDensity

/-! # Dense Open -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.DenseOpen.Construction

noncomputable section

/-! A nonempty open in an integral scheme over a Dedekind domain is dense
in every fiber after removing one proper closed subset of the base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem integral_scheme_open_dense_in_fibers_after_shrinking
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (X : Over (Spec (.of R))) [IsIntegral X.left]
    [CompactSpace X.left] [IsLocallyNoetherian X.left]
    (U : X.left.Opens) (hU : (U : Set X.left).Nonempty) :
    ∃ r : R, r ≠ 0 ∧
      ∀ (S : Type u) [CommRing S] [Algebra R S], IsUnit (algebraMap R S r) →
        Dense ((pullback.fst X.hom
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))) ⁻¹' (U : Set X.left)) := by
  classical
  obtain ⟨ι, hι, V, hV, hcover⟩ := FiniteAffineCover.Construction.finite_nonempty_affine_open_cover X.left
  let : Fintype ι := Fintype.ofFinite ι
  let Y (i : ι) := OpenOver.Construction.overOpen X (V i)
  let Ui (i : ι) : (Y i).left.Opens := (V i).ι ⁻¹ᵁ U
  have hlocal (i : ι) : ∃ r : R, r ≠ 0 ∧
      ∀ (S : Type u) [CommRing S] [Algebra R S], IsUnit (algebraMap R S r) →
        Dense ((pullback.fst (Y i).hom
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))) ⁻¹' (Ui i : Set (Y i).left)) := by
    have : IsAffine (Y i).left := (hV i).1
    have : Nonempty (V i).toScheme := ⟨⟨(hV i).2.choose, (hV i).2.choose_spec⟩⟩
    have hVI : IsIntegral (V i).toScheme := isIntegral_of_isOpenImmersion (V i).ι
    have : IsIntegral (Y i).left := hVI
    have : IsLocallyNoetherian (Y i).left := inferInstanceAs (IsLocallyNoetherian (V i).toScheme)
    apply SchemeFiberDensity.Construction.affine_scheme_open_dense_in_fibers_after_shrinking R (Y i) (Ui i)
    obtain ⟨x, hxV, hxU⟩ := nonempty_preirreducible_inter (V i).isOpen U.isOpen (hV i).2 hU
    exact ⟨⟨x, hxV⟩, hxU⟩
  choose r hr hd using hlocal
  let a : R := ∏ i, r i
  have ha : a ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hr i)
  refine ⟨a, ha, fun S _ _ hu ↦ ?_⟩
  let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let F := Over.pullback g
  let j (i : ι) := (F.map (OpenOver.Construction.overOpenInclusion X (V i))).left
  have hj (i : ι) : Set.range (j i) = (pullback.fst X.hom g) ⁻¹' (V i : Set X.left) := by
    have H := FoundationsPullback.Constructions.pullback_over_map_isPullback g (OpenOver.Construction.overOpenInclusion X (V i))
    simpa only [OpenOver.Construction.overOpenInclusion_range] using GeometricFieldComponents.Construction.pullback_square_range_fst H
  apply SchemeFiberDensity.Construction.dense_of_covering_scheme_maps (fun i ↦ (F.obj (Y i)).left) j
  · intro x
    have hx : pullback.fst X.hom g x ∈ ⨆ i, V i := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    have hm : x ∈ Set.range (j i) := (hj i).symm ▸ hi
    obtain ⟨y, hy⟩ := hm
    exact ⟨i, y, hy⟩
  · intro i
    have hui : IsUnit (algebraMap R S (r i)) :=
      isUnit_of_dvd_unit ((algebraMap R S).map_dvd
        (Finset.dvd_prod_of_mem r (Finset.mem_univ i))) hu
    have hi := hd i S hui
    have hcomp : j i ≫ pullback.fst X.hom g = pullback.fst (Y i).hom g ≫ (V i).ι :=
      (FoundationsPullback.Constructions.pullback_over_map_isPullback g (OpenOver.Construction.overOpenInclusion X (V i))).w
    change Dense ((j i ≫ pullback.fst X.hom g) ⁻¹' (U : Set X.left))
    rw [hcomp]
    exact hi

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.DenseOpen.Construction
