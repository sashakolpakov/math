import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Proper
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.Topology.Connected.TotallyDisconnected

/-! # Proper Functions Eq -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperFunctionsEq.Construction.ProperFunctions

/-!
# Maps from proper connected schemes to affine schemes

The scheme-theoretic image is affine and proper over the field, hence
finite. Connectedness therefore forces the map to be constant on
underlying points. This is the properness input for the divisor argument
for multiplication in the characteristic.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem finite_of_proper_affine {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsAffineHom f] : IsFinite f := by
  have : IsIntegralHom f := IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr
    ⟨inferInstance, inferInstance⟩
  exact IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _ |>.mpr
    ⟨inferInstance, inferInstance⟩

theorem finite_image {K : Type u} [Field K] {X Y : Over (Spec (.of K))}
    [IsProper X.hom] [IsAffine Y.left] [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) : IsFinite (f.left.imageι ≫ Y.hom) := by
  have : IsProper (f.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  have : IsProper f.left := IsProper.of_comp f.left Y.hom
  have : IsProper (f.left.imageι ≫ Y.hom) := by
    have : IsProper (f.left.toImage ≫ f.left.imageι ≫ Y.hom) := by
      rw [Scheme.Hom.toImage_imageι_assoc]
      infer_instance
    exact Proper.Construction.Geometry.proper_of_comp f.left.toImage (f.left.imageι ≫ Y.hom)
  have : IsAffine f.left.image := isAffine_of_isAffineHom f.left.imageι
  exact finite_of_proper_affine _

theorem apply_eq {K : Type u} [Field K] {X Y : Over (Spec (.of K))}
    [IsProper X.hom] [ConnectedSpace X.left]
    [IsAffine Y.left] [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (x y : X.left) : f.left x = f.left y := by
  have : IsProper (f.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  have : IsProper f.left := IsProper.of_comp f.left Y.hom
  have := finite_image f
  have : IsLocallyArtinian f.left.image :=
    IsLocallyArtinian.of_locallyQuasiFinite (f.left.imageι ≫ Y.hom)
  have : ConnectedSpace f.left.image := f.left.toImage.surjective.connectedSpace
    f.left.toImage.continuous
  have : Subsingleton f.left.image := subsingleton_of_preconnected_totallyDisconnected
  have he : f.left.toImage x = f.left.toImage y := Subsingleton.elim _ _
  have hx : f.left.imageι (f.left.toImage x) = f.left x :=
    congrArg (fun g => g x) f.left.toImage_imageι
  have hy : f.left.imageι (f.left.toImage y) = f.left y :=
    congrArg (fun g => g y) f.left.toImage_imageι
  exact hx.symm.trans ((congrArg f.left.imageι he).trans hy)

/-- A global function on a proper connected reduced scheme over a field
is either zero or invertible. -/
theorem section_eq_zero_or_isUnit {K : Type u} [Field K]
    (X : Over (Spec (.of K))) [IsProper X.hom] [ConnectedSpace X.left] [IsReduced X.left]
    (a : Γ(X.left, ⊤)) : a = 0 ∨ IsUnit a := by
  let c : CommRingCat.of K ⟶ Γ(X.left, ⊤) := (Scheme.ΓSpecIso (.of K)).inv ≫ X.hom.appTop
  let e : CommRingCat.of (Polynomial K) ⟶ Γ(X.left, ⊤) :=
    CommRingCat.ofHom (Polynomial.eval₂RingHom c.hom a)
  let C : CommRingCat.of K ⟶ CommRingCat.of (Polynomial K) := CommRingCat.ofHom Polynomial.C
  let Y := Over.mk (Spec.map C)
  let f : X.left ⟶ Y.left := X.left.toSpecΓ ≫ Spec.map e
  have hw : f ≫ Y.hom = X.hom := by
    change X.left.toSpecΓ ≫ Spec.map e ≫ Spec.map C = X.hom
    rw [← Spec.map_comp]
    have heC : C ≫ e = c := CommRingCat.hom_ext (Polynomial.eval₂RingHom_comp_C c.hom a)
    rw [heC]
    change X.left.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of K)).inv ≫ X.hom.appTop) = _
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
      Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have : IsAffine Y.left := by dsimp [Y]; infer_instance
  have : IsSeparated Y.hom := by dsimp [Y]; infer_instance
  have : LocallyOfFiniteType Y.hom := by
    change LocallyOfFiniteType (Spec.map C)
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact (RingHom.finiteType_algebraMap (A := K) (B := Polynomial K)).mpr inferInstance
  have hf (x y : X.left) : f x = f y := apply_eq (Over.homMk f hw : X ⟶ Y) x y
  have hpre : f ⁻¹ᵁ PrimeSpectrum.basicOpen (Polynomial.X : Polynomial K) = X.left.basicOpen a := by
    change X.left.toSpecΓ ⁻¹ᵁ (Spec.map e ⁻¹ᵁ PrimeSpectrum.basicOpen Polynomial.X) = _
    rw [SpecMap_preimage_basicOpen, Scheme.toSpecΓ_preimage_basicOpen]
    exact congrArg X.left.basicOpen (Polynomial.eval₂_X c.hom a)
  by_cases hne : (X.left.basicOpen a : Set X.left).Nonempty
  · right
    obtain ⟨x, hx⟩ := hne
    apply X.left.toRingedSpace.isUnit_of_isUnit_germ
    intro y hy
    apply (X.left.mem_basicOpen a y hy).mp
    rw [← hpre]
    change f y ∈ PrimeSpectrum.basicOpen (Polynomial.X : Polynomial K)
    rw [hf y x]
    change x ∈ f ⁻¹ᵁ PrimeSpectrum.basicOpen (Polynomial.X : Polynomial K)
    rw [hpre]
    exact hx
  · left
    apply eq_zero_of_basicOpen_eq_bot a
    apply le_antisymm _ bot_le
    intro x hx
    exact (hne ⟨x, hx⟩).elim

theorem globalSections_isField {K : Type u} [Field K]
    (X : Over (Spec (.of K))) [IsProper X.hom] [ConnectedSpace X.left] [IsReduced X.left] :
    IsField Γ(X.left, ⊤) := by
  have : Nontrivial Γ(X.left, ⊤) := (X.left.presheaf.germ ⊤
    (Nonempty.some (inferInstance : Nonempty X.left)) trivial).hom.domain_nontrivial
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro a ha
  exact ((section_eq_zero_or_isUnit X a).resolve_left ha).exists_right_inv

/-- A rational point identifies the global-function field with the base
field through the actual structure map on global sections. -/
theorem isIso_appTop_of_section {K : Type u} [Field K]
    (X : Over (Spec (.of K))) [IsProper X.hom] [ConnectedSpace X.left] [IsReduced X.left]
    (e : Spec (.of K) ⟶ X.left) (he : e ≫ X.hom = 𝟙 _) : IsIso X.hom.appTop := by
  let := (globalSections_isField X).toField
  have hi : Function.Injective e.appTop := e.appTop.hom.injective
  have : Mono e.appTop := ConcreteCategory.mono_of_injective _ hi
  have hc : X.hom.appTop ≫ e.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, he, Scheme.Hom.id_appTop]
  have hc' : e.appTop ≫ X.hom.appTop = 𝟙 _ := by
    apply (cancel_mono e.appTop).mp
    rw [Category.assoc, hc, Category.comp_id, Category.id_comp]
  exact ⟨⟨e.appTop, hc, hc'⟩⟩

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperFunctionsEq.Construction.ProperFunctions
