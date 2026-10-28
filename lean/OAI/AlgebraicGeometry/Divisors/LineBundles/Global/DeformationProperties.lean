import OAI.AlgebraicGeometry.Divisors.LineBundles.QuotientFiber
import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Topology.Sets.OpenCover

/-! # Deformation Properties -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationProperties.BundleCycles

noncomputable section

/-!
# LineBundleCycles: geometric properties of the global deformation

The affine chart pullback squares prove that the global structural map is
affine. Noetherianity then follows from the actual Noetherian extended-Rees
algebras and compactness over a Noetherian base.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u

/-- Evaluation at t = 1 on the actual extended-Rees subalgebra. -/
def deformationAtOne {R : Type u} [CommRing R] (J : Ideal R) :
    Deformation.Iff.BundleCycles.deformationAlgebra J →+* R :=
  (LaurentPolynomial.eval₂ (RingHom.id R) (1 : Rˣ)).comp (Deformation.Iff.BundleCycles.deformationAlgebra J).val.toRingHom

theorem deformationAtOne_algebraMap {R : Type u} [CommRing R] (J : Ideal R) :
    (deformationAtOne J).comp (algebraMap R (Deformation.Iff.BundleCycles.deformationAlgebra J)) = RingHom.id R := by
  apply RingHom.ext
  intro r
  exact LaurentPolynomial.eval₂_C _ _ r

/-- A target-local morphism property can be checked on specified pullback charts. -/
theorem morphismProperty_of_cover_pullbacks (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] {A B : Scheme.{u}} (f : A ⟶ B)
    (C : B.OpenCover) (Z : C.I₀ → Scheme.{u}) (a : ∀ i, Z i ⟶ A)
    (b : ∀ i, Z i ⟶ C.X i)
    (h : ∀ i, IsPullback (b i) (a i) (C.f i) f)
    (hb : ∀ i, P (b i)) : P f := by
  apply IsZariskiLocalAtTarget.of_openCover (P := P) C
  intro i
  let hi := (h i).flip
  have hc : P (hi.isoPullback.inv ≫ b i) :=
    (P.cancel_left_of_respectsIso _ _).mpr (hb i)
  exact (congrArg (fun k => P k) hi.isoPullback_inv_snd).mp hc

variable {X : Scheme.{u}} (I : X.IdealSheafData)

instance affineBaseRing_noetherian [IsLocallyNoetherian X] (U : X.AffineZariskiSite) :
    IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U

instance globalDeformationCover_isAffine (U : X.AffineZariskiSite) :
    IsAffine ((Deformation.BundleCycles.globalDeformationCover I).X U) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)))))

instance globalDeformationCover_isOpenImmersion (U : X.AffineZariskiSite) :
    IsOpenImmersion ((Deformation.BundleCycles.globalDeformationCover I).f U) :=
  (Deformation.BundleCycles.globalDeformationCover I).map_prop U

/-- The inverse image of a base affine open is exactly its deformation chart. -/
theorem globalDeformationProjection_preimage (U : X.AffineZariskiSite) :
    Deformation.BundleCycles.globalDeformationProjection I ⁻¹ᵁ U.1 = ((Deformation.BundleCycles.globalDeformationCover I).f U).opensRange := by
  have h := (Deformation.BundleCycles.deformationGlueData I).toBase_preimage_eq_opensRange_ι U
  change Deformation.BundleCycles.globalDeformationProjection I ⁻¹ᵁ U.1.ι.opensRange =
    ((Deformation.BundleCycles.globalDeformationCover I).f U).opensRange at h
  rw [Scheme.Opens.opensRange_ι] at h
  exact h

/-- The actual global deformation is affine over its original base. -/
instance globalDeformationProjection_isAffineHom :
    IsAffineHom (Deformation.BundleCycles.globalDeformationProjection I) := by
  constructor
  intro U hU
  let V : X.AffineZariskiSite := ⟨U, hU⟩
  have he : Deformation.BundleCycles.globalDeformationProjection I ⁻¹ᵁ U =
      ((Deformation.BundleCycles.globalDeformationCover I).f V).opensRange :=
    globalDeformationProjection_preimage I V
  exact he.symm ▸ isAffineOpen_opensRange ((Deformation.BundleCycles.globalDeformationCover I).f V)

/-- Noetherianity of the coefficient rings gives local Noetherianity of the gluing. -/
instance globalDeformation_isLocallyNoetherian [IsLocallyNoetherian X] :
    IsLocallyNoetherian (Deformation.BundleCycles.globalDeformation I) := by
  have : ∀ U, IsAffine ((Deformation.BundleCycles.globalDeformationCover I).X U) :=
    fun U => globalDeformationCover_isAffine I U
  apply (isLocallyNoetherian_iff_of_affine_openCover (Deformation.BundleCycles.globalDeformationCover I)).mpr
  intro U
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  exact isNoetherianRing_of_ringEquiv (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U))
    (Scheme.ΓSpecIso (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)))).symm.commRingCatIsoToRingEquiv

/-- Over a Noetherian scheme the global deformation is itself Noetherian. -/
instance globalDeformation_isNoetherian [AlgebraicGeometry.IsNoetherian X] :
    AlgebraicGeometry.IsNoetherian (Deformation.BundleCycles.globalDeformation I) := by
  have : CompactSpace (Deformation.BundleCycles.globalDeformation I) :=
    QuasiCompact.compactSpace_of_compactSpace (Deformation.BundleCycles.globalDeformationProjection I)
  exact ⟨⟩

/-- Evaluation at one supplies an actual section of each affine deformation chart. -/
def deformationChartSection (U : X.AffineZariskiSite) :
    U.1.toScheme ⟶ (Deformation.BundleCycles.globalDeformationCover I).X U :=
  U.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (deformationAtOne (I.ideal U)))

theorem deformationChartSection_toBase (U : X.AffineZariskiSite) :
    deformationChartSection I U ≫ (Deformation.BundleCycles.deformationGlueData I).natTrans.app U = 𝟙 U.1.toScheme := by
  let a : Γ(X, U.1) ⟶ CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)) :=
    CommRingCat.ofHom (algebraMap Γ(X, U.1) (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)))
  let b : CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)) ⟶ Γ(X, U.1) :=
    CommRingCat.ofHom (deformationAtOne (I.ideal U))
  have hab : a ≫ b = 𝟙 Γ(X, U.1) :=
    CommRingCat.hom_ext (deformationAtOne_algebraMap (I.ideal U))
  have hs : Spec.map b ≫ Spec.map a = 𝟙 (Spec Γ(X, U.1)) :=
    (Spec.map_comp a b).symm.trans ((congrArg Spec.map hab).trans (Spec.map_id _))
  change (U.2.isoSpec.hom ≫ Spec.map b) ≫ (Spec.map a ≫ U.2.isoSpec.inv) = _
  rw [Category.assoc, ← Category.assoc (Spec.map b), hs, Category.id_comp, U.2.isoSpec.hom_inv_id]

/-- Every base point has a point above it in the deformation, namely at t = 1. -/
theorem globalDeformationProjection_surjective : Function.Surjective (Deformation.BundleCycles.globalDeformationProjection I) := by
  intro x
  let U : X.AffineZariskiSite := (directedCover X).idx x
  obtain ⟨y, hy⟩ := (directedCover X).covers x
  let z := deformationChartSection I U y
  refine ⟨(Deformation.BundleCycles.globalDeformationCover I).f U z, ?_⟩
  have hbase := congrArg (fun k => k z) ((Deformation.BundleCycles.deformationGlueData I).ι_toBase U)
  have hsection := congrArg (fun k => k y) (deformationChartSection_toBase I U)
  change (Deformation.BundleCycles.deformationGlueData I).natTrans.app U z = y at hsection
  change Deformation.BundleCycles.globalDeformationProjection I ((Deformation.BundleCycles.globalDeformationCover I).f U z) =
    U.1.ι ((Deformation.BundleCycles.deformationGlueData I).natTrans.app U z) at hbase
  exact hbase.trans ((congrArg U.1.ι hsection).trans hy)

/-- Empty affine base opens may be discarded without losing any deformation point. -/
def nonemptyDeformationCover : (Deformation.BundleCycles.globalDeformation I).OpenCover :=
  Scheme.Cover.mkOfCovers {U : X.AffineZariskiSite // Nonempty U.1}
    (fun U => (Deformation.BundleCycles.globalDeformationCover I).X U.1)
    (fun U => (Deformation.BundleCycles.globalDeformationCover I).f U.1)
    (by
      intro x
      obtain ⟨U, y, rfl⟩ := (Deformation.BundleCycles.globalDeformationCover I).exists_eq x
      exact ⟨⟨U, ⟨(Deformation.BundleCycles.deformationGlueData I).natTrans.app U y⟩⟩, y, rfl⟩)
    (fun U => globalDeformationCover_isOpenImmersion I U.1)

instance nonemptyDeformationCover_isIntegral [IsIntegral X]
    (U : (nonemptyDeformationCover I).I₀) :
    IsIntegral ((nonemptyDeformationCover I).X U) := by
  have : Nonempty U.1.1 := U.2
  have : IsDomain Γ(X, U.1.1) := inferInstance
  exact inferInstanceAs (IsIntegral (Spec (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U.1)))))

instance globalDeformation_isReduced [IsIntegral X] : IsReduced (Deformation.BundleCycles.globalDeformation I) := by
  have : ∀ U, IsReduced ((nonemptyDeformationCover I).X U) := fun U => by
    have := nonemptyDeformationCover_isIntegral I U
    infer_instance
  exact IsReduced.of_openCover (Deformation.BundleCycles.globalDeformation I) (nonemptyDeformationCover I)

/-- Any two retained deformation charts intersect above their nonempty base intersection. -/
theorem nonemptyDeformationCover_pairwise_inter [IsIntegral X] :
    Pairwise (fun U V : (nonemptyDeformationCover I).I₀ =>
      ¬ Disjoint ((nonemptyDeformationCover I).f U).opensRange
        ((nonemptyDeformationCover I).f V).opensRange) := by
  intro U V _
  obtain ⟨x, hxU, hxV⟩ := nonempty_preirreducible_inter U.1.1.isOpen V.1.1.isOpen
    (Set.nonempty_coe_sort.mp U.2) (Set.nonempty_coe_sort.mp V.2)
  obtain ⟨y, hy⟩ := globalDeformationProjection_surjective I x
  have hU : y ∈ ((nonemptyDeformationCover I).f U).opensRange := by
    change y ∈ ((Deformation.BundleCycles.globalDeformationCover I).f U.1).opensRange
    rw [← globalDeformationProjection_preimage I U.1]
    change Deformation.BundleCycles.globalDeformationProjection I y ∈ U.1.1
    exact hy.symm ▸ hxU
  have hV : y ∈ ((nonemptyDeformationCover I).f V).opensRange := by
    change y ∈ ((Deformation.BundleCycles.globalDeformationCover I).f V.1).opensRange
    rw [← globalDeformationProjection_preimage I V.1]
    change Deformation.BundleCycles.globalDeformationProjection I y ∈ V.1.1
    exact hy.symm ▸ hxV
  intro hd
  exact Set.disjoint_left.mp (TopologicalSpace.Opens.coe_disjoint.mpr hd) hU hV

/-- Integrality of the base implies integrality of its actual global deformation. -/
instance globalDeformation_isIntegral [IsIntegral X] : IsIntegral (Deformation.BundleCycles.globalDeformation I) := by
  have hpre : ∀ U : (nonemptyDeformationCover I).I₀,
      IsPreirreducible (((nonemptyDeformationCover I).f U).opensRange : Set (Deformation.BundleCycles.globalDeformation I)) := by
    intro U
    have := nonemptyDeformationCover_isIntegral I U
    have h := (IrreducibleSpace.isIrreducible_univ ((nonemptyDeformationCover I).X U)).2.image
      ((nonemptyDeformationCover I).f U) ((nonemptyDeformationCover I).f U).continuous.continuousOn
    simp only [Set.image_univ] at h
    exact h
  have : PreirreducibleSpace (Deformation.BundleCycles.globalDeformation I) := ⟨IsPreirreducible.of_subset_iUnion
    (nonemptyDeformationCover_pairwise_inter I) hpre isOpen_univ
    (by
      change Set.univ ⊆ ⋃ U, Set.range ((nonemptyDeformationCover I).f U)
      rw [(nonemptyDeformationCover I).iUnion_range])⟩
  have : Nonempty (Deformation.BundleCycles.globalDeformation I) := by
    obtain ⟨y, _⟩ := globalDeformationProjection_surjective I (Classical.choice (inferInstance : Nonempty X))
    exact ⟨y⟩
  have : IrreducibleSpace (Deformation.BundleCycles.globalDeformation I) :=
    { toPreirreducibleSpace := inferInstance, toNonempty := inferInstance }
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationProperties.BundleCycles
