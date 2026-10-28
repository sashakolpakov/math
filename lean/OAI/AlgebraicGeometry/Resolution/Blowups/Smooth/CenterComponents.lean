import OAI.AlgebraicGeometry.Resolution.Blowups.Open.ImmersionSmoothImage
import Mathlib.Topology.NoetherianSpace
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MixedBoundary

/-! # Center Components -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterComponents.Construction

noncomputable section

section

/-! Irreducible components of a smooth complex scheme are disjoint integral open and closed subschemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem smooth_complex_scheme_isReduced {X : Scheme}
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] : IsReduced X := by
  choose Y j hj hY hs y hy using Open.ImmersionSmoothImage.Construction.smooth_complex_pointed_integral_chart f
  let : ∀ x, IsOpenImmersion (j x) := hj
  let C : X.OpenCover := Scheme.Cover.mkOfCovers X Y j (fun x => ⟨x, y x, hy x⟩)
    (fun _ => inferInstance)
  let : ∀ i : C.I₀, IsReduced (C.X i) := fun i => by
    let : IsIntegral (Y i) := hY i
    exact inferInstanceAs (IsReduced (Y i))
  exact IsReduced.of_openCover X C

theorem smooth_complex_irreducible_component_open {X : Scheme}
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (C : Set X) (hC : C ∈ irreducibleComponents X) : IsOpen C := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨Y, j, hj, hY, hs, y, hy⟩ := Open.ImmersionSmoothImage.Construction.smooth_complex_pointed_integral_chart f x
  let : IsOpenImmersion j := hj
  let : IsIntegral Y := hY
  have hp := preimage_mem_irreducibleComponents hC j.isOpenEmbedding ⟨x, hx, y, hy⟩
  rw [irreducibleComponents_eq_singleton] at hp
  have he : j ⁻¹' C = Set.univ := Set.mem_singleton_iff.mp hp
  refine ⟨Set.range j, ?_, j.isOpenEmbedding.isOpen_range, ⟨y, hy⟩⟩
  rintro _ ⟨z, rfl⟩
  have hz : z ∈ j ⁻¹' C := by rw [he]; trivial
  exact hz

theorem smooth_complex_irreducible_components_disjoint {X : Scheme}
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (C D : Set X)
    (hC : C ∈ irreducibleComponents X) (hD : D ∈ irreducibleComponents X) (hne : C ≠ D) :
    Disjoint C D := by
  apply Set.disjoint_left.mpr
  intro x hxC hxD
  have hDC : D ⊆ C :=
    (subset_closure_inter_of_isPreirreducible_of_isOpen hD.1.2
      (smooth_complex_irreducible_component_open f C hC) ⟨x, hxD, hxC⟩).trans
      (closure_minimal Set.inter_subset_right (isClosed_of_mem_irreducibleComponents C hC))
  exact hne (Set.Subset.antisymm (hD.2 hC.1 hDC) hDC)

def smoothIntegralComponentOpen {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (C : irreducibleComponents X) : X.Opens :=
  ⟨C.val, smooth_complex_irreducible_component_open f C.val C.property⟩

theorem smoothIntegralComponentOpen_isIntegral {X : Scheme}
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (C : irreducibleComponents X) :
    IsIntegral (smoothIntegralComponentOpen f C).toScheme := by
  let : IsReduced X := smooth_complex_scheme_isReduced f
  let : IrreducibleSpace (smoothIntegralComponentOpen f C).toScheme :=
    isIrreducible_iff_irreducibleSpace.mp C.property.1
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem smoothIntegralComponentOpen_cover {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] :
    ⨆ C : irreducibleComponents X, smoothIntegralComponentOpen f C = ⊤ := by
  apply top_le_iff.mp
  intro x _
  exact Opens.mem_iSup.mpr ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩,
    mem_irreducibleComponent⟩

theorem smoothIntegralComponentOpen_closedImmersion {X : Scheme}
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (C : irreducibleComponents X) :
    IsClosedImmersion (smoothIntegralComponentOpen f C).ι := by
  apply IsClosedImmersion.iff_isPreimmersion.mpr
  refine ⟨inferInstance, ?_⟩
  change IsClosed (Set.range (Subtype.val : (smoothIntegralComponentOpen f C) → X))
  rw [Subtype.range_coe]
  exact isClosed_of_mem_irreducibleComponents C.val C.property

theorem smoothIntegralComponents_finite {X : Scheme} [NoetherianSpace X] :
    (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents

end

/-! Smooth center components as actual native ideal sheaves on the ambient scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.IdealSheafData) [Smooth (I.subschemeι ≫ f)]

abbrev smoothCenterComponentFintype [NoetherianSpace I.subscheme] :
    Fintype (irreducibleComponents I.subscheme) :=
  (smoothIntegralComponents_finite (X := I.subscheme)).fintype

def smoothCenterComponentEmbedding (C : irreducibleComponents I.subscheme) :
    (smoothIntegralComponentOpen (I.subschemeι ≫ f) C).toScheme ⟶ X :=
  (smoothIntegralComponentOpen (I.subschemeι ≫ f) C).ι ≫ I.subschemeι

instance smoothCenterComponentEmbedding_closedImmersion (C : irreducibleComponents I.subscheme) :
    IsClosedImmersion (smoothCenterComponentEmbedding f I C) := by
  let : IsClosedImmersion (smoothIntegralComponentOpen (I.subschemeι ≫ f) C).ι :=
    smoothIntegralComponentOpen_closedImmersion (I.subschemeι ≫ f) C
  unfold smoothCenterComponentEmbedding
  infer_instance

def smoothCenterComponentIdeal (C : irreducibleComponents I.subscheme) : X.IdealSheafData :=
  (smoothCenterComponentEmbedding f I C).ker

theorem smoothCenterComponentIdeal_contains (C : irreducibleComponents I.subscheme) :
    I ≤ smoothCenterComponentIdeal f I C := by
  have h := (smoothIntegralComponentOpen (I.subschemeι ≫ f) C).ι.le_ker_comp I.subschemeι
  rw [Scheme.IdealSheafData.ker_subschemeι] at h
  exact h

theorem smoothCenterComponentIdeal_integral (C : irreducibleComponents I.subscheme) :
    IsIntegral (smoothCenterComponentIdeal f I C).subscheme := by
  let : IsIntegral (smoothIntegralComponentOpen (I.subschemeι ≫ f) C).toScheme :=
    smoothIntegralComponentOpen_isIntegral (I.subschemeι ≫ f) C
  exact Integral.SchemeImage.Construction.scheme_image_isIntegral (smoothCenterComponentEmbedding f I C)

theorem smoothCenterComponentIdeal_smooth (C : irreducibleComponents I.subscheme) :
    Smooth ((smoothCenterComponentIdeal f I C).subschemeι ≫ f) := by
  let : Smooth (smoothCenterComponentEmbedding f I C ≫ f) := by
    unfold smoothCenterComponentEmbedding
    rw [Category.assoc]
    infer_instance
  exact Global.PointedSmoothCenter.Construction.kernel_subscheme_smooth_of_closed_immersion (smoothCenterComponentEmbedding f I C) f

def smoothCenterComponentOpenCover : I.subscheme.OpenCover :=
  Scheme.Cover.mkOfCovers (irreducibleComponents I.subscheme)
    (fun C => (smoothIntegralComponentOpen (I.subschemeι ≫ f) C).toScheme)
    (fun C => (smoothIntegralComponentOpen (I.subschemeι ≫ f) C).ι)
    (fun x => ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩,
      ⟨x, mem_irreducibleComponent⟩, rfl⟩) (fun _ => inferInstance)

theorem smoothCenterComponentIdeal_iInf :
    ⨅ C : irreducibleComponents I.subscheme, smoothCenterComponentIdeal f I C = I := by
  have h := I.subschemeι.iInf_ker_openCover_map_comp (smoothCenterComponentOpenCover f I)
  rw [Scheme.IdealSheafData.ker_subschemeι] at h
  exact h

theorem smoothCenterComponentEmbedding_disjoint
    (C D : irreducibleComponents I.subscheme) (hne : C ≠ D) :
    Disjoint (Set.range (smoothCenterComponentEmbedding f I C))
      (Set.range (smoothCenterComponentEmbedding f I D)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨c, hc⟩ ⟨d, hd⟩
  have he : c.val = d.val := I.subschemeι.injective (hc.trans hd.symm)
  have hdis := smooth_complex_irreducible_components_disjoint (I.subschemeι ≫ f)
    C.val D.val C.property D.property (fun h => hne (Subtype.ext h))
  exact Set.disjoint_left.mp hdis c.property (he ▸ d.property)

theorem smoothCenterComponentIdeal_support (C : irreducibleComponents I.subscheme) :
    ((smoothCenterComponentIdeal f I C).support : Set X) =
      Set.range (smoothCenterComponentEmbedding f I C) := by
  rw [smoothCenterComponentIdeal, Scheme.Hom.support_ker]
  exact (smoothCenterComponentEmbedding f I C).isClosedEmbedding.isClosed_range.closure_eq

theorem smoothCenterComponentIdeal_sup (C D : irreducibleComponents I.subscheme) (hne : C ≠ D) :
    smoothCenterComponentIdeal f I C ⊔ smoothCenterComponentIdeal f I D = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  rw [Scheme.IdealSheafData.support_sup]
  apply SetLike.coe_injective
  change ((smoothCenterComponentIdeal f I C).support : Set X) ∩
    ((smoothCenterComponentIdeal f I D).support : Set X) = ∅
  rw [smoothCenterComponentIdeal_support, smoothCenterComponentIdeal_support]
  exact Set.disjoint_iff_inter_eq_empty.mp (smoothCenterComponentEmbedding_disjoint f I C D hne)

theorem smoothCenterComponentIdeal_ne_bot (hI : I ≠ ⊥) (C : irreducibleComponents I.subscheme) :
    smoothCenterComponentIdeal f I C ≠ ⊥ := by
  intro h
  exact hI (le_bot_iff.mp (h ▸ smoothCenterComponentIdeal_contains f I C))

theorem smoothCenterComponentIdeal_permissible (J : X.IdealSheafData) (b : ℕ)
    (hJ : J ≤ I ^ b) (C : irreducibleComponents I.subscheme) :
    J ≤ smoothCenterComponentIdeal f I C ^ b :=
  hJ.trans (pow_le_pow_left' (smoothCenterComponentIdeal_contains f I C) b)

theorem smoothCenterComponentIdeal_prod [Fintype (irreducibleComponents I.subscheme)] :
    ∏ C : irreducibleComponents I.subscheme, smoothCenterComponentIdeal f I C = I := by
  classical
  calc
    _ = ⨅ C : irreducibleComponents I.subscheme, smoothCenterComponentIdeal f I C := by
      ext1
      funext U
      rw [Global.MixedBoundary.Construction.idealSheaf_finset_prod_ideal, Scheme.IdealSheafData.ideal_iInf, iInf_apply]
      change (∏ C, (smoothCenterComponentIdeal f I C).ideal U) =
        ⨅ C, (smoothCenterComponentIdeal f I C).ideal U
      have hcop : (↑(Finset.univ : Finset (irreducibleComponents I.subscheme)) :
          Set (irreducibleComponents I.subscheme)).Pairwise
          (fun C D => IsCoprime ((smoothCenterComponentIdeal f I C).ideal U)
            ((smoothCenterComponentIdeal f I D).ideal U)) := by
        intro C _ D _ hne
        apply Ideal.isCoprime_iff_sup_eq.mpr
        have h := congrArg (fun K : X.IdealSheafData => K.ideal U) (smoothCenterComponentIdeal_sup f I C D hne)
        exact h
      simpa only [Finset.mem_univ, iInf_true] using Ideal.prod_eq_iInf_of_pairwise_isCoprime hcop
    _ = I := smoothCenterComponentIdeal_iInf f I

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterComponents.Construction
