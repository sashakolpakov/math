import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolynomialEtaleCoordinates
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DifferentialBasisNeighborhood
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OverPullbackCartesianMap
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Smooth.Fiber

/-! # Etale Smooth -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleSmooth.EtaleSmoothLocus

noncomputable section

/-! Smoothness descends through an étale source neighborhood. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry TensorProduct KaehlerDifferential _root_.Module

/-- Flatness over the original base descends through a faithfully flat extension. -/
theorem flat_of_faithfullyFlat_tower
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Module.FaithfullyFlat A B] [Module.Flat R B] : Module.Flat R A := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro M N _ _ _ _ f hf
  change Function.Injective (f.baseChange A)
  rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective A B]
  intro x y h
  apply (AlgebraTensorModule.cancelBaseChange R A B B M).injective
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := B) f hf
  have hc := AlgebraTensorModule.lTensor_comp_cancelBaseChange R A B (M := B) f
  have hcx := DFunLike.congr_fun hc x
  have hcy := DFunLike.congr_fun hc y
  exact hcx.trans ((congrArg (AlgebraTensorModule.cancelBaseChange R A B B N) h).trans
    hcy.symm)

theorem smooth_of_differential_coordinates_and_etale_cover
    (R A B : Type*) [CommRing R] [IsNoetherianRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FiniteType R A] [Module.FaithfullyFlat A B]
    [Algebra.Etale A B] [Algebra.Smooth R B]
    {ι : Type} [Finite ι] (a : ι → A) (b : Basis ι A Ω[A⁄R])
    (hb : ∀ i, b i = D R A (a i)) : Algebra.Smooth R A := by
  let P := MvPolynomial ι R
  let φ : P →ₐ[R] A := MvPolynomial.aeval a
  let : Algebra P A := φ.toRingHom.toAlgebra
  let : Algebra P B := (IsScalarTower.toAlgHom R A B |>.comp φ).toRingHom.toAlgebra
  have : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have : IsScalarTower P A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R P B := IsScalarTower.to₁₂₄ R P A B
  let c := (b.baseChange B).map (tensorKaehlerEquivOfFormallyEtale R A B)
  have hc (i : ι) : c i = D R B (algebraMap P B (MvPolynomial.X i)) := by
    simp only [c, Basis.map_apply, Basis.baseChange_apply,
      tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, hb, map_D]
    congr 1
    change algebraMap A B (a i) = algebraMap A B (MvPolynomial.aeval a (MvPolynomial.X i))
    rw [MvPolynomial.aeval_X]
  have : Algebra.FormallyEtale P B :=
    PELModuli.IntegralModel.PolynomialEtaleCoordinates.polynomial_coordinates_formallyEtale R B ι c hc
  have : Algebra.FiniteType P A := Algebra.FiniteType.of_restrictScalars_finiteType R P A
  have : Algebra.FiniteType P B := Algebra.FiniteType.of_restrictScalars_finiteType R P B
  have : Algebra.FinitePresentation P A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.FinitePresentation P B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale P B := ⟨inferInstance, inferInstance⟩
  have : Algebra.FormallyUnramified P A := by
    constructor
    have : Subsingleton (B ⊗[A] Ω[A⁄P]) :=
      (tensorKaehlerEquivOfFormallyEtale P A B).subsingleton
    exact Module.FaithfullyFlat.lTensor_reflects_triviality A B _
  have : Module.Flat P A := flat_of_faithfullyFlat_tower P A B
  have : Algebra.Etale P A := Algebra.Etale.of_formallyUnramified_of_flat
  have : Algebra.Smooth R P := ⟨inferInstance, inferInstance⟩
  exact Algebra.Smooth.comp R P A

/-- Smoothness of a finite-type algebra over a noetherian ring descends
through an arbitrary faithfully flat étale algebra. -/
theorem smooth_algebra_of_etale_cover
    (R A B : Type) [CommRing R] [IsNoetherianRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FiniteType R A] [Module.FaithfullyFlat A B]
    [Algebra.Etale A B] [Algebra.Smooth R B] : Algebra.Smooth R A := by
  have : Algebra.FinitePresentation R A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Module.Flat A Ω[A⁄R] := PELModuli.IntegralModel.SmoothEtaleDifferentials.differentials_flat_of_faithfully_flat_etale_cover R A B
  refine ⟨Algebra.smoothLocus_eq_univ_iff.mp (Set.eq_univ_iff_forall.mpr fun p => ?_), inferInstance⟩
  obtain ⟨g, hg, ι, hι, a, b, hb⟩ := PELModuli.IntegralModel.DifferentialBasisNeighborhood.exists_differential_basis_neighborhood R A p.asIdeal
  have : Finite ι := hι
  let Ag := Localization.Away g
  let Bg := Ag ⊗[A] B
  let : Algebra B Bg := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower R B Bg := IsScalarTower.to₁₃₄ R A B Bg
  have : IsLocalization.Away (algebraMap A B g) Bg := inferInstance
  have : Algebra.Smooth B Bg := Algebra.Smooth.of_isLocalization_Away (algebraMap A B g)
  have : Algebra.Smooth R Bg := Algebra.Smooth.comp R B Bg
  have hs : Algebra.Smooth R Ag :=
    smooth_of_differential_coordinates_and_etale_cover R Ag Bg
      (fun i => algebraMap A Ag (a i)) b hb
  exact Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hs hg

theorem smooth_of_etale_cover_affine
    {X Y S : Scheme.{0}} [IsAffine X] [IsAffine Y] [IsAffine S]
    [IsLocallyNoetherian S] (q : X ⟶ Y) (f : Y ⟶ S)
    [Etale q] [Surjective q] [LocallyOfFiniteType f] [Smooth (q ≫ f)] : Smooth f := by
  let R := Γ(S, ⊤)
  let A := Γ(Y, ⊤)
  let B := Γ(X, ⊤)
  let : Algebra R A := f.appTop.hom.toAlgebra
  let : Algebra A B := q.appTop.hom.toAlgebra
  let : Algebra R B := (q.appTop.hom.comp f.appTop.hom).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.FaithfullyFlat A B :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine q).mp ⟨inferInstance, inferInstance⟩
  have : Algebra.Etale A B := HasRingHomProperty.appTop (P := @Etale) q inferInstance
  have : Algebra.FiniteType R A :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f inferInstance
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  have : Algebra.Smooth R B := HasRingHomProperty.appTop (P := @Smooth) (q ≫ f) inferInstance
  have h : f.appTop.hom.Smooth := smooth_algebra_of_etale_cover R A B
  have : Smooth (Spec.map f.appTop) := (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr h
  have heq : f = Y.isoSpec.hom ≫ Spec.map f.appTop ≫ S.isoSpec.inv := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [heq]
  infer_instance

theorem image_mem_smoothLocus_affine
    {X Y S : Scheme.{0}} [IsAffine X] [IsAffine Y] [IsAffine S]
    [IsLocallyNoetherian S] (q : X ⟶ Y) (f : Y ⟶ S)
    [Etale q] [LocallyOfFiniteType f] [Smooth (q ≫ f)] (x : X) :
    q x ∈ f.smoothLocus := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVr⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_range_self x) q.isOpenMap.isOpen_range
  change Y.Opens at V
  have : IsAffine V := hV
  have : IsAffine (q ⁻¹ᵁ V).toScheme := hV.preimage q
  have : Surjective (q ∣_ V) := by
    constructor
    intro y
    obtain ⟨z, hz⟩ := hVr y.property
    refine ⟨⟨z, ?_⟩, ?_⟩
    · change q z ∈ V
      simpa only [hz] using y.property
    · apply Subtype.ext
      simpa only [← Scheme.Hom.resLE_eq_morphismRestrict,
        Scheme.Hom.coe_resLE_apply] using hz
  have : Smooth ((q ∣_ V) ≫ V.ι ≫ f) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    infer_instance
  have : Smooth (V.ι ≫ f) := smooth_of_etale_cover_affine (q ∣_ V) (V.ι ≫ f)
  have h : (⟨q x, hxV⟩ : V) ∈ (V.ι ≫ f).smoothLocus := by
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  rwa [← Scheme.Hom.preimage_smoothLocus_eq V.ι f] at h

/-- A smooth étale source neighborhood maps into the target's actual smooth locus. -/
theorem image_mem_smoothLocus
    {X Y S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
    (q : X ⟶ Y) (f : Y ⟶ S) [Etale q] [LocallyOfFiniteType f]
    [Smooth (q ≫ f)] (x : X) : q x ∈ f.smoothLocus := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, _⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (q x)) isOpen_univ
  change Y.Opens at V
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV (q ⁻¹ᵁ V).isOpen
  change X.Opens at W
  change W ≤ q ⁻¹ᵁ V at hWV
  have : IsAffine V := hV
  have : IsAffine W := hW
  have : Smooth (q.resLE V W hWV ≫ V.ι ≫ f) := by
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
    infer_instance
  have h := image_mem_smoothLocus_affine (q.resLE V W hWV) (V.ι ≫ f) ⟨x, hxW⟩
  rw [← Scheme.Hom.preimage_smoothLocus_eq V.ι f] at h
  change (q.resLE V W hWV ⟨x, hxW⟩).val ∈ f.smoothLocus at h
  simpa only [Scheme.Hom.coe_resLE_apply] using h

theorem smooth_on_smoothLocus
    {X S : Scheme.{0}} (f : X ⟶ S) [LocallyOfFinitePresentation f] :
    Smooth (f.smoothLocus.ι ≫ f) := by
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  rw [← Scheme.Hom.preimage_smoothLocus_eq]
  exact top_le_iff.mp fun x _ => x.property

/-- Étale maps pull back the smooth locus exactly. Both sides use the formal
smoothness of the actual morphisms on local rings, including nilpotents. -/
theorem preimage_smoothLocus_eq
    {X Y S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
    (q : X ⟶ Y) (f : Y ⟶ S) [Etale q] [LocallyOfFiniteType f] :
    q ⁻¹ᵁ f.smoothLocus = (q ≫ f).smoothLocus := by
  ext x
  constructor
  · intro hx
    change (f.stalkMap (q x)).hom.FormallySmooth at hx
    have hq : (q.stalkMap x).hom.FormallySmooth := by
      have h : x ∈ q.smoothLocus := by
        rw [Scheme.Hom.smoothLocus_eq_top]
        trivial
      exact h
    change (((q ≫ f).stalkMap x :
      S.presheaf.stalk (f (q x)) ⟶ X.presheaf.stalk x)).hom.FormallySmooth
    rw [Scheme.Hom.stalkMap_comp]
    exact hx.comp hq
  · intro hx
    let U := (q ≫ f).smoothLocus
    have : Smooth (U.ι ≫ (q ≫ f)) := smooth_on_smoothLocus (q ≫ f)
    have : Smooth ((U.ι ≫ q) ≫ f) := by
      simpa only [Category.assoc] using (inferInstance : Smooth (U.ι ≫ (q ≫ f)))
    exact image_mem_smoothLocus (U.ι ≫ q) f ⟨x, hx⟩

/-- The two images of a point in an étale span are simultaneously smooth. -/
theorem mem_smoothLocus_iff_of_etale_span
    {S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
    {U X : Over S} (p q : U ⟶ X) [Etale p.left] [Etale q.left]
    [LocallyOfFiniteType X.hom] (u : U.left) :
    p.left u ∈ X.hom.smoothLocus ↔ q.left u ∈ X.hom.smoothLocus := by
  change u ∈ p.left ⁻¹ᵁ X.hom.smoothLocus ↔ u ∈ q.left ⁻¹ᵁ X.hom.smoothLocus
  rw [EtaleSmoothLocus.preimage_smoothLocus_eq p.left X.hom, EtaleSmoothLocus.preimage_smoothLocus_eq q.left X.hom]
  simp only [p.w, q.w]

instance locallyOfFiniteType_overPullback
    {S T : Scheme.{0}} (b : T ⟶ S) (X : Over S) [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType ((Over.pullback b).obj X).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd X.hom b))

/-- A point with specified base map gives its original point in the native base change. -/
def baseChangePoint {S T : Scheme.{0}} (b : T ⟶ S) {X : Over S}
    (x : Over.mk b ⟶ X) : Over.mk (𝟙 T) ⟶ (Over.pullback b).obj X :=
  Over.homMk (pullback.lift x.left (𝟙 T) (x.w.trans (Category.id_comp b).symm))
    (pullback.lift_snd _ _ _)

theorem baseChangePoint_comp {S T : Scheme.{0}} (b : T ⟶ S)
    {U X : Over S} (u : Over.mk b ⟶ U) (p : U ⟶ X) :
    baseChangePoint b (u ≫ p) = baseChangePoint b u ≫ (Over.pullback b).map p := by
  apply Over.OverMorphism.ext
  change pullback.lift (u.left ≫ p.left) (𝟙 T) _ =
    pullback.lift u.left (𝟙 T) _ ≫
      pullback.lift (pullback.fst U.hom b ≫ p.left) (pullback.snd U.hom b) _
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc]

/-- Étale-span invariance after arbitrary base change to an affine noetherian base,
with the two original point maps retained by the pullback universal property. -/
theorem baseChangePoint_mem_smoothLocus_iff_of_etale_span
    {S T : Scheme.{0}} [IsAffine T] [IsLocallyNoetherian T] (b : T ⟶ S)
    {U X : Over S} (p q : U ⟶ X) [Etale p.left] [Etale q.left]
    [LocallyOfFiniteType X.hom] (u : Over.mk b ⟶ U) (t : T) :
    (baseChangePoint b (u ≫ p)).left t ∈ ((Over.pullback b).obj X).hom.smoothLocus ↔
      (baseChangePoint b (u ≫ q)).left t ∈ ((Over.pullback b).obj X).hom.smoothLocus := by
  have : Etale ((Over.pullback b).map p).left :=
    MorphismProperty.of_isPullback (OverPullbackCartesianMap.overPullback_map_isPullback b p).flip inferInstance
  have : Etale ((Over.pullback b).map q).left :=
    MorphismProperty.of_isPullback (OverPullbackCartesianMap.overPullback_map_isPullback b q).flip inferInstance
  rw [baseChangePoint_comp b u p, baseChangePoint_comp b u q]
  exact mem_smoothLocus_iff_of_etale_span ((Over.pullback b).map p)
    ((Over.pullback b).map q) ((baseChangePoint b u).left t)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleSmooth.EtaleSmoothLocus
