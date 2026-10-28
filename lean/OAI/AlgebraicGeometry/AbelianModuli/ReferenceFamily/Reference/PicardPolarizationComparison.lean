import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PolarizedConstruction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.PoincareIso
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.ComplexFibers
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPeriod
import OAI.RepresentationTheory.Theta.Geometric.LinePeriodPairing

/-! # Picard Polarization Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardPolarizationComparison.ReferencePicardConstruction

noncomputable section

/-! The actual reference Poincare class detects dual period maps.
Preservation of the constructed Chern form therefore preserves the
original reference polarization isogeny. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.RepresentationTheory.Theta.Geometric.LinePeriodPairing

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} {P : Datum.RankThreePELDatum E s} {z w : P.domain}
    {F : Fiber.ReferenceAnalyticFiber P z} {G : Fiber.ReferenceAnalyticFiber P w} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {D : DualModel.ReferenceDualModel F hP}
    {W : AlgebraicModel.ReferenceAlgebraicModel G hP} {D' : DualModel.ReferenceDualModel G hP}
    {p : IsogenyKernel.ReferenceLatticeIsogeny M D} {q : IsogenyKernel.ReferenceLatticeIsogeny W D'}

local instance : IsMonHom (show M.abelian.toOver ⟶ D.abelian.toOver from p.isogeny.hom) :=
  p.isogeny.preservesGroup
local instance : IsFinite (show M.abelian.toOver ⟶ D.abelian.toOver from p.isogeny.hom).left :=
  p.isogeny.finite
local instance : IsMonHom (show W.abelian.toOver ⟶ D'.abelian.toOver from q.isogeny.hom) :=
  q.isogeny.preservesGroup

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction.ReferencePicardConstruction.referencePeriodPairing (C : PicardConstruction.ReferencePicardConstruction p) :
    Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods D.abelian →ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian →ₗ[ℚ] ℚ :=
  RepresentationTheory.Theta.Geometric.LinePeriodPairing.linePeriodPairing D.abelian M.abelian (HilbertConstruction.Line.Bundles.LineBundle.classOf C.poincare)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction.ReferencePicardConstruction.referencePeriodPairing_isogeny (C : PicardConstruction.ReferencePicardConstruction p) (x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) :
    C.referencePeriodPairing (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (show M.abelian.toOver ⟶ D.abelian.toOver from p.isogeny.hom) x) y =
      Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine x y := by
  let f : M.abelian.toOver ⟶ D.abelian.toOver := p.isogeny.hom
  have hp := RepresentationTheory.Theta.Geometric.LinePeriodPairing.linePeriodPairing_pullback M.abelian M.abelian D.abelian M.abelian f (𝟙 M.abelian.toOver)
    (HilbertConstruction.Line.Bundles.LineBundle.classOf C.poincare) x y
  rw [Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_id] at hp
  have he := RepresentationTheory.Theta.Geometric.LinePeriodPairing.linePeriodPairing_biextension M.abelian C.ampleLine
    (C.poincare.pullback (f ⊗ₘ 𝟙 M.abelian.toOver).left)
    (RepresentationTheory.Theta.Geometric.QuotientDifferenceFibers.quotientDifference_formulaIso p.isogeny C.ampleLine C.poincare C.difference)
  exact hp.symm.trans (LinearMap.congr_fun (LinearMap.congr_fun he x) y)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction.ReferencePicardConstruction.referenceIsogeny_period_bijective :
    Function.Bijective (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (show M.abelian.toOver ⟶ D.abelian.toOver from p.isogeny.hom)) := by
  let f : M.abelian.toOver ⟶ D.abelian.toOver := p.isogeny.hom
  have hf := Finite.ComplexFibers.NativeLinearMaps.rationalLift_injective_of_isFinite f
  have hd : Module.finrank ℚ (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) = Module.finrank ℚ (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods D.abelian) := by
    rw [Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods_finrank, Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods_finrank, M.dimension, D.dimension]
  exact ((Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f).linearEquivOfInjective hf hd).bijective

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction.ReferencePicardConstruction.referencePeriodPairing_left_ext (C : PicardConstruction.ReferencePicardConstruction p) (x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods D.abelian)
    (h : ∀ v, C.referencePeriodPairing x v = C.referencePeriodPairing y v) : x = y := by
  obtain ⟨u, rfl⟩ := (PicardConstruction.ReferencePicardConstruction.referenceIsogeny_period_bijective (p := p)).surjective x
  obtain ⟨v, rfl⟩ := (PicardConstruction.ReferencePicardConstruction.referenceIsogeny_period_bijective (p := p)).surjective y
  apply congrArg (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (show M.abelian.toOver ⟶ D.abelian.toOver from p.isogeny.hom))
  apply sub_eq_zero.mp
  apply Intrinsic.ChernPeriod.nativeChernForm_separating M.abelian C.ampleLine C.ample
  intro t
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
  exact (C.referencePeriodPairing_isogeny u t).symm.trans ((h t).trans (C.referencePeriodPairing_isogeny v t))

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction.ReferencePicardConstruction.referencePeriodPairing_detects (C : PicardConstruction.ReferencePicardConstruction p) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f g : A.toOver ⟶ D.abelian.toOver) [IsMonHom f] [IsMonHom g]
    (h : ∀ x y, C.referencePeriodPairing (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f x) y = C.referencePeriodPairing (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift g x) y) : f = g := by
  apply Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_faithful f g
  exact LinearMap.ext (fun x => C.referencePeriodPairing_left_ext _ _ (h x))

variable (C : PicardConstruction.ReferencePicardConstruction p) (C' : PicardConstruction.ReferencePicardConstruction q)
    (e : M.abelianScheme.scheme ≅ W.abelianScheme.scheme) [heGroup : IsMonHom e.hom]

local instance : IsMonHom (show M.abelian.toOver ⟶ W.abelian.toOver from e.hom) := heGroup
local instance : IsMonHom (show D.abelian.toOver ⟶ D'.abelian.toOver from (Dual.UnderlyingIso.dualFamilyIso C.dual C'.dual e).hom) :=
  Dual.UnderlyingIso.dualFamilyIso_isMonHom C.dual C'.dual e

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction.ReferencePicardConstruction.referenceDualPeriodPairing
    (x : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods D.abelian) (y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) :
    C'.referencePeriodPairing (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (Dual.UnderlyingIso.dualFamilyIso C.dual C'.dual e).hom x) (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom y) =
      C.referencePeriodPairing x y := by
  have h := RepresentationTheory.Theta.Geometric.LinePeriodPairing.linePeriodPairing_pullback D.abelian M.abelian D'.abelian W.abelian
    (Dual.UnderlyingIso.dualFamilyIso C.dual C'.dual e).hom e.hom (HilbertConstruction.Line.Bundles.LineBundle.classOf C'.poincare) x y
  exact h.symm.trans (congrArg (fun Q => RepresentationTheory.Theta.Geometric.LinePeriodPairing.linePeriodPairing D.abelian M.abelian Q x y)
    (Dual.PoincareIso.dualFamilyIso_poincare C.dual C'.dual e))

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction.ReferencePicardConstruction.polarizationIso_of_reference_chern
    (he : ∀ x y, Intrinsic.ChernPairing.nativeChernForm W.abelian C'.ampleLine (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom x) (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom y) =
      Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine x y) :
    p.isogeny.hom ≫ (Dual.UnderlyingIso.dualFamilyIso C.dual C'.dual e).hom = e.hom ≫ q.isogeny.hom := by
  let f : M.abelian.toOver ⟶ W.abelian.toOver := e.hom
  let d : D.abelian.toOver ⟶ D'.abelian.toOver := (Dual.UnderlyingIso.dualFamilyIso C.dual C'.dual e).hom
  let a : M.abelian.toOver ⟶ D.abelian.toOver := p.isogeny.hom
  let b : W.abelian.toOver ⟶ D'.abelian.toOver := q.isogeny.hom
  let : IsMonHom f := heGroup
  let : IsMonHom d := Dual.UnderlyingIso.dualFamilyIso_isMonHom C.dual C'.dual e
  let : IsMonHom a := p.isogeny.preservesGroup
  let : IsMonHom b := q.isogeny.preservesGroup
  change a ≫ d = f ≫ b
  apply C'.referencePeriodPairing_detects M.abelian
  intro x t
  obtain ⟨y, rfl⟩ := (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLiftIso (show M.abelian.toOver ≅ W.abelian.toOver from e)).surjective t
  rw [Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp]
  change C'.referencePeriodPairing
      (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (Dual.UnderlyingIso.dualFamilyIso C.dual C'.dual e).hom (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift p.isogeny.hom x)) (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom y) =
    C'.referencePeriodPairing (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift q.isogeny.hom (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom x)) (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom y)
  rw [C.referenceDualPeriodPairing C' e, C.referencePeriodPairing_isogeny, C'.referencePeriodPairing_isogeny]
  exact (he x y).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardPolarizationComparison.ReferencePicardConstruction
