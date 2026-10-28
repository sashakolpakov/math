import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MixedKoszulGeometricSupport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberScalar
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.ParameterKoszulResolution

/-! # Koszul Germ Support -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.KoszulGermSupport

noncomputable section

/-! Germs of actual frame coordinates define exactly the inverse
image of the common zero set in the local spectrum. A finite zero set
on a Jacobson scheme therefore gives support only at the closed point. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {X : Scheme.{u}}

theorem fromSpecStalk_preimage_basicOpen (x : X) (r : Γ(X, ⊤)) :
    X.fromSpecStalk x ⁻¹ᵁ X.basicOpen r =
      PrimeSpectrum.basicOpen (X.presheaf.germ ⊤ x trivial r) := by
  rw [(X.fromSpecStalk x).preimage_basicOpen_top, basicOpen_eq_of_affine']
  have h : (X.fromSpecStalk x).appTop ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom =
      X.presheaf.germ ⊤ x trivial := by
    rw [FiberScalar.FiberScalarMaps.fromStalk_appTop, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg PrimeSpectrum.basicOpen (ConcreteCategory.congr_hom h r)

theorem framedKoszul_germ_zeroLocus (x : X) (bs : List (LineBundleKoszulComplex.LineBundleSection X))
    (ρ : LineBundleKoszulComplex.LineBundleSection X → X.presheaf.stalk x)
    (hframe : ∀ b ∈ bs, ∃ e : b.1.sheaf ≅ Line.Bundles.structureModule X,
      X.presheaf.germ ⊤ x trivial (Frame.Coordinates.structureModuleEndValue X (b.2 ≫ e.hom)) = ρ b) :
    PrimeSpectrum.zeroLocus (Regular.SequenceBasic.Ideal.ofList (bs.map ρ) : Set (X.presheaf.stalk x)) =
      (X.fromSpecStalk x) ⁻¹' MixedKoszulGeometricSupport.mixedSectionZeroSet bs := by
  have hopen (b : LineBundleKoszulComplex.LineBundleSection X) (hb : b ∈ bs) :
      X.fromSpecStalk x ⁻¹ᵁ Ample.LineBundles.sectionNonvanishing b.2 = PrimeSpectrum.basicOpen (ρ b) := by
    obtain ⟨e, he⟩ := hframe b hb
    have hb := (Ample.Powers.sectionNonvanishing_comp_iso b.2 e).symm.trans
      (Scalar.Nonvanishing.sectionNonvanishing_scalar (b.2 ≫ e.hom))
    rw [hb, fromSpecStalk_preimage_basicOpen, he]
  rw [Regular.SequenceBasic.Ideal.ofList, PrimeSpectrum.zeroLocus_span]
  ext y
  change (∀ r, r ∈ bs.map ρ → r ∈ y.asIdeal) ↔
    ∀ b ∈ bs, X.fromSpecStalk x y ∉ Ample.LineBundles.sectionNonvanishing b.2
  constructor
  · intro h b hb
    have hy : y ∉ PrimeSpectrum.basicOpen (ρ b) :=
      not_not.mpr (h _ (List.mem_map.mpr ⟨b, hb, rfl⟩))
    rw [← hopen b hb] at hy
    exact hy
  · intro h r hr
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr
    have hy : y ∉ X.fromSpecStalk x ⁻¹ᵁ Ample.LineBundles.sectionNonvanishing b.2 := h b hb
    rw [hopen b hb] at hy
    exact not_not.mp hy

theorem framedKoszul_germ_support_closedPoint [JacobsonSpace X]
    (x : X) (bs : List (LineBundleKoszulComplex.LineBundleSection X)) (hfinite : (MixedKoszulGeometricSupport.mixedSectionZeroSet bs).Finite)
    (ρ : LineBundleKoszulComplex.LineBundleSection X → X.presheaf.stalk x)
    (hframe : ∀ b ∈ bs, ∃ e : b.1.sheaf ≅ Line.Bundles.structureModule X,
      X.presheaf.germ ⊤ x trivial (Frame.Coordinates.structureModuleEndValue X (b.2 ≫ e.hom)) = ρ b) :
    PrimeSpectrum.zeroLocus (Regular.SequenceBasic.Ideal.ofList (bs.map ρ) : Set (X.presheaf.stalk x)) ⊆
      {IsLocalRing.closedPoint (X.presheaf.stalk x)} := by
  rw [framedKoszul_germ_zeroLocus x bs ρ hframe]
  intro y hy
  exact MixedKoszulGeometricSupport.finiteClosedSet_stalk_preimage_eq_closedPoint
    (MixedKoszulGeometricSupport.mixedSectionZeroSet bs) (MixedKoszulGeometricSupport.mixedSectionZeroSet_isClosed bs) hfinite x y hy

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.KoszulGermSupport
