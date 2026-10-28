import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ThetaConstructionIntegralAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ThetaConstructionPolarization
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicCoordinatePeriodModel
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicChernClassDetection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.PoincareIso
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincarePeriodPairing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IsogenyComparisonKernel

/-! # Integral Polarization Type -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralPolarizationType

noncomputable section

/-! The integral Chern matrix of an original polarized abelian variety
has that variety's specified polarization type. The identification uses
the actual primitive dual and the original geometric kernel labels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.ThetaConstruction.DefinitionsIntegral

section Comparison

variable {g N : ℕ} {δ : Fin g → ℕ} {J : Picard.ThetaConstruction.DefinitionsIntegral.IntegralMatrix g}
    {T : Picard.ThetaConstruction.DefinitionsIntegral.MarkedPolarizedTorus g J} (M : Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel T)
    {D : Picard.ThetaConstruction.IntegralDualModel.Geometric.IntegralDualAlgebraicModel T} {p : Picard.ThetaConstruction.IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny M D}
    (C : Picard.ThetaConstruction.PrimitiveDual.Geometric.PrimitiveDualConstruction p)
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (e : M.abelianScheme.scheme ≅ A.abelian.scheme) [he : IsMonHom e.hom]

local instance : IsMonHom (show M.abelian.toOver ⟶
    (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)).toOver from e.hom) := he

/-- Equality of the actual Chern forms identifies the primitive
polarization with the original one, under the represented dual map. -/
theorem primitive_polarization_comparison
    (hchern : ∀ x y : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian,
      ChernPairing.nativePolarizationForm A
        (IntegralMaps.IntrinsicLinearMaps.rationalLift (show M.abelian.toOver ⟶
          (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)).toOver from e.hom) x)
        (IntegralMaps.IntrinsicLinearMaps.rationalLift (show M.abelian.toOver ⟶
          (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)).toOver from e.hom) y) =
      ChernPairing.nativeChernForm M.abelian C.ampleLine x y) :
    p.isogeny.hom ≫ (Dual.UnderlyingIso.dualFamilyIso C.dual A.dual e).hom =
      e.hom ≫ A.polarization.isogeny.hom := by
  let B := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
  let DA := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.dual.abelian (Dual.Projectivity.dualNativeProjectivePresentation A)
  let f : M.abelian.toOver ⟶ B.toOver := e.hom
  let d : D.abelian.toOver ⟶ DA.toOver := (Dual.UnderlyingIso.dualFamilyIso C.dual A.dual e).hom
  let a : M.abelian.toOver ⟶ D.abelian.toOver := p.isogeny.hom
  let b : B.toOver ⟶ DA.toOver := A.polarization.isogeny.hom
  let : IsMonHom f := he
  let : IsMonHom d := Dual.UnderlyingIso.dualFamilyIso_isMonHom C.dual A.dual e
  let : IsMonHom a := p.isogeny.preservesGroup
  let : IsMonHom b := A.polarization.isogeny.preservesGroup
  have hd (x : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods D.abelian) (y : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) :
      PoincarePeriodPairing.nativePoincarePeriodPairing A (IntegralMaps.IntrinsicLinearMaps.rationalLift d x) (IntegralMaps.IntrinsicLinearMaps.rationalLift f y) =
        ThetaConstructionIntegralAction.periodPairing M C x y := by
    have hp := RepresentationTheory.Theta.Geometric.LinePeriodPairing.linePeriodPairing_pullback D.abelian M.abelian DA B d f
      (HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare) x y
    exact hp.symm.trans (congrArg
      (fun Q => RepresentationTheory.Theta.Geometric.LinePeriodPairing.linePeriodPairing D.abelian M.abelian Q x y)
      (Dual.PoincareIso.dualFamilyIso_poincare C.dual A.dual e))
  have hb : Polarization.PeriodIso.nativePolarizationMap A = b := by
    apply Over.OverMorphism.ext
    exact Polarization.PeriodIso.nativePolarizationMap_left A
  change a ≫ d = f ≫ b
  apply PoincarePeriodPairing.nativePoincarePeriodPairing_detects_group_maps A M.abelian
  intro x z
  obtain ⟨y, rfl⟩ :=
    (IntegralMaps.IntrinsicLinearMaps.rationalLiftIso (show M.abelian.toOver ≅ B.toOver from e)).surjective z
  rw [IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, IntegralMaps.IntrinsicLinearMaps.rationalLift_comp]
  change PoincarePeriodPairing.nativePoincarePeriodPairing A (IntegralMaps.IntrinsicLinearMaps.rationalLift d (IntegralMaps.IntrinsicLinearMaps.rationalLift a x)) (IntegralMaps.IntrinsicLinearMaps.rationalLift f y) =
    PoincarePeriodPairing.nativePoincarePeriodPairing A (IntegralMaps.IntrinsicLinearMaps.rationalLift b (IntegralMaps.IntrinsicLinearMaps.rationalLift f x)) (IntegralMaps.IntrinsicLinearMaps.rationalLift f y)
  rw [hd, ThetaConstructionIntegralAction.periodPairing_isogeny]
  have h := PoincarePeriodPairing.nativePoincarePeriodPairing_polarization A (IntegralMaps.IntrinsicLinearMaps.rationalLift f x) (IntegralMaps.IntrinsicLinearMaps.rationalLift f y)
  change PoincarePeriodPairing.nativePoincarePeriodPairing A
    (IntegralMaps.IntrinsicLinearMaps.rationalLift (Polarization.PeriodIso.nativePolarizationMap A) (IntegralMaps.IntrinsicLinearMaps.rationalLift f x)) (IntegralMaps.IntrinsicLinearMaps.rationalLift f y) = _ at h
  rw [IntegralMaps.IntrinsicLinearMaps.rationalLift_congr (A := B) (B := DA) (Polarization.PeriodIso.nativePolarizationMap A) b hb] at h
  exact (hchern x y).symm.trans h.symm

end Comparison

attribute [local implicit_reducible] Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.abelianScheme
  Picard.ThetaConstruction.IntegralDualModel.Geometric.IntegralDualAlgebraicModel.abelianScheme Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native Picard.ThetaConstruction.IntrinsicCoordinatePeriodModel.Geometric.nativeCoordinatePeriodModel
  Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.toOver

variable {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (Picard.ThetaConstruction.DefinitionsIntegral.Index g) (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)))

/-- The cokernel labels come from the original polarization kernel,
transported through the marked discriminant and the actual dual torus. -/
theorem nativeIntegralChernMatrix_cokernel_labels :
    Nonempty
      (((((Picard.ThetaConstruction.DefinitionsIntegral.Index g → ℤ) →ₗ[ℤ] ℤ) ⧸
          (Matrix.toBilin' (ChernIntegralPeriods.nativeIntegralChernMatrix
            (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))
            (ChernPairing.polarizationLineBundle A) b)).range)) ≃+
        ((∀ i : Fin g, ZMod (δ i)) × (∀ i : Fin g, ZMod (δ i)))) := by
  let B := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
  let L : HilbertConstruction.Line.Bundles.LineBundle B.toOver.left := ChernPairing.polarizationLineBundle A
  let hL : L.IsAmple := ChernPairing.polarizationLineBundle_ample A
  obtain ⟨T, u, _hperiod, hlattice, hform, _hkernel⟩ :=
    ThetaConstructionPolarization.nativeThetaConstruction_polarized_comparison B L hL b
  let M := Picard.ThetaConstruction.IntrinsicCoordinatePeriodModel.Geometric.nativeCoordinatePeriodModel B L hL T u hlattice
  obtain ⟨D, p, ⟨C⟩⟩ := Picard.ThetaConstruction.PrimitiveDual.Geometric.exists_primitive_dual_on_actual_model M
    (ChernIntegralPeriods.nativeIntegralChernMatrix_alternating B L b)
  let e : M.abelianScheme.scheme ≅ A.abelian.scheme :=
    Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
  let : IsMonHom e.hom := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso_isMonHom A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
  have he : (show B.toOver ⟶ B.toOver from e.hom) = 𝟙 B.toOver := by
    apply Over.OverMorphism.ext
    rfl
  let : IsMonHom (show B.toOver ⟶ B.toOver from e.hom) := by
    rw [he]
    infer_instance
  have heperiod : IntegralMaps.IntrinsicLinearMaps.rationalLift (show B.toOver ⟶ B.toOver from e.hom) = LinearMap.id :=
    (IntegralMaps.IntrinsicLinearMaps.rationalLift_congr (A := B) (B := B) _ _ he).trans (IntegralMaps.IntrinsicLinearMaps.rationalLift_id B)
  have hchern : ChernPairing.nativeChernForm B L = ChernPairing.nativeChernForm M.abelian C.ampleLine := by
    apply M.nativeIntegralPeriod_bilinear_ext
    intro l m
    exact (Picard.ThetaConstruction.IntrinsicCoordinatePeriodModel.Geometric.nativeCoordinatePeriodModel_chern B L hL T u hlattice hform l m).trans
      (C.chern l m).symm
  have hp := primitive_polarization_comparison M C A e (by
    intro x y
    rw [heperiod]
    exact LinearMap.congr_fun (LinearMap.congr_fun hchern x) y)
  let d : D.abelianScheme.scheme ≅ A.dual.abelian.scheme := Dual.UnderlyingIso.dualFamilyIso C.dual A.dual e
  let : IsMonHom d.hom := Dual.UnderlyingIso.dualFamilyIso_isMonHom C.dual A.dual e
  let : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  let : IsMonHom d.symm.hom := inferInstanceAs (IsMonHom d.inv)
  have hcomparison : e.inv ≫ p.isogeny.hom = A.polarization.isogeny.hom ≫ d.inv := by
    apply (cancel_mono d.hom).mp
    calc
      (e.inv ≫ p.isogeny.hom) ≫ d.hom = e.inv ≫ (p.isogeny.hom ≫ d.hom) :=
        Category.assoc _ _ _
      _ = e.inv ≫ (e.hom ≫ A.polarization.isogeny.hom) :=
        congrArg (fun q => e.inv ≫ q) hp
      _ = A.polarization.isogeny.hom := by simp only [Iso.inv_hom_id_assoc]
      _ = (A.polarization.isogeny.hom ≫ d.inv) ≫ d.hom := by
        rw [Category.assoc, d.inv_hom_id, Category.comp_id]
  have htype : p.isogeny.HasPolarizationType δ :=
    IsogenyComparisonKernel.isogeny_type_of_comparison (A := A.abelian) (B := M.abelianScheme)
      (D := A.dual.abelian) (E := D.abelianScheme)
      A.polarization.isogeny p.isogeny e.symm d.symm
      hcomparison A.polarization.kernelType
  let labels := (htype.geometricKernel ℂ (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)).some
  exact ⟨T.markedDiscriminantEquiv.toAddEquiv.symm.trans
    (T.discriminantKernelEquiv.trans
      (p.complexKernelEquiv.toAdditive.trans labels.toAdditive))⟩

def nativeIntegralPolarizationType (hpos : ∀ i, 0 < δ i)
    (horder : ∀ i j, i ≤ j → δ i ∣ δ j) :
    Picard.ThetaConstruction.PolarizationTypeData.Geometric.IntegralPolarizationType (ChernIntegralPeriods.nativeIntegralChernMatrix
      (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)) (ChernPairing.polarizationLineBundle A) b) where
  elementaryDivisors := δ
  positive := hpos
  ordered := horder
  cokernel := (nativeIntegralChernMatrix_cokernel_labels A b).some

@[simp] theorem nativeIntegralPolarizationType_elementaryDivisors
    (hpos : ∀ i, 0 < δ i) (horder : ∀ i j, i ≤ j → δ i ∣ δ j) :
    (nativeIntegralPolarizationType A b hpos horder).elementaryDivisors = δ := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralPolarizationType
