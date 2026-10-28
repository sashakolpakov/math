import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.LatticeTransport
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.ChartQuotient
import OAI.RepresentationTheory.Theta.Geometric.ParametrizedQuotient

/-! # Torus Map -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! A fixed central torus maps to every nearby actual fiber through
the original exponential and the exact real period-frame transport. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold ContDiff _root_.Topology

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

local instance IntrinsicFrame.TorusMap.nativeFrameCentralTorus_nativeRealLieGroup (z : Intrinsic.FamilyFrames.FamilyChartBase C) [IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left] :
    LieGroup (𝓘(ℝ, Intrinsic.FamilyFrames.FamilyChartModel C z)) ∞ (Intrinsic.FamilyFrames.FamilyChartPoints C z) :=
  ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberLieGroup.Abelian.nativeScheme_realLieGroup (Intrinsic.FamilyFrames.familyChartFiber C z).scheme

variable (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

abbrev Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.CentralTorus := Intrinsic.FamilyFrames.FamilyChartTangent C ⧸ F.centralLattice.toAddSubgroup

def Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.centralTorusHomeomorph
    (present : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C (Intrinsic.FamilyFrames.familyChartCenter C))) :
    F.CentralTorus ≃ₜ Intrinsic.FamilyFrames.FamilyChartPoints C (Intrinsic.FamilyFrames.familyChartCenter C) := by
  let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left := F.integral
  let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C z) := F.t2
  let : ConnectedSpace (Intrinsic.FamilyFrames.FamilyChartPoints C (Intrinsic.FamilyFrames.familyChartCenter C)) := present.connectedSpace
  have hc := F.chartData (Intrinsic.FamilyFrames.familyChartCenter C) (Family.ChartOpenImage.familyChartCenter_mem C)
  exact Intrinsic.ChartQuotient.nativeChartQuotientHomeomorph (F.charts (Intrinsic.FamilyFrames.familyChartCenter C)) hc.2.2.1 hc.1 hc.2.1

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.centralTorusHomeomorph_mk
    (present : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (v : Intrinsic.FamilyFrames.FamilyChartTangent C) :
    let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left := F.integral
    let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C z) := F.t2
    F.centralTorusHomeomorph present (QuotientAddGroup.mk v) =
      ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (G := Intrinsic.FamilyFrames.FamilyChartPoints C (Intrinsic.FamilyFrames.familyChartCenter C))
        (E := Intrinsic.FamilyFrames.FamilyChartModel C (Intrinsic.FamilyFrames.familyChartCenter C)) (F.charts (Intrinsic.FamilyFrames.familyChartCenter C)) v := rfl

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.centralTorus_compact
    (present : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C (Intrinsic.FamilyFrames.familyChartCenter C))) :
    CompactSpace F.CentralTorus := by
  let : CompactSpace (Intrinsic.FamilyFrames.FamilyChartPoints C (Intrinsic.FamilyFrames.familyChartCenter C)) := present.compactSpace
  exact (F.centralTorusHomeomorph present).symm.compactSpace

def Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.transportedExponential (z : Intrinsic.FamilyFrames.FamilyChartBase C) :
    Intrinsic.FamilyFrames.FamilyChartTangent C →+ Additive (Intrinsic.FamilyFrames.FamilyChartPoints C z) := by
  let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C w).scheme.left := F.integral
  let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C w) := F.t2
  exact {
    toFun := fun v => Additive.ofMul
      (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := Intrinsic.FamilyFrames.FamilyChartModel C z) (F.charts z) (F.realTransport z v))
    map_zero' := by rw [map_zero, ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential_zero]; rfl
    map_add' := by intro v w; rw [map_add, ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential_add]; rfl }

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.transportedExponential_kernel (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood) :
    F.centralLattice.toAddSubgroup ≤ (F.transportedExponential z).ker := by
  let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C w).scheme.left := F.integral
  let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C w) := F.t2
  intro v hv
  have h := (F.realTransport_lattice z hz v).mpr hv
  exact h

def Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.centralTorusFamilyMap (U : Set (Intrinsic.FamilyFrames.FamilyChartBase C)) (hU : U ⊆ F.neighborhood) :
    U × F.CentralTorus → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) :=
  ParametrizedQuotient.parametrizedQuotientMap F.centralLattice.toAddSubgroup
    (fun z : U => F.transportedExponential z)
    (fun z : U => F.transportedExponential_kernel z (hU z.property))
    (fun z : U => fun y : Additive (Intrinsic.FamilyFrames.FamilyChartPoints C z) =>
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (Intrinsic.FamilyFrames.familyChartParameter C z)) y.toMul)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.centralTorusFamilyMap_mk (U : Set (Intrinsic.FamilyFrames.FamilyChartBase C)) (hU : U ⊆ F.neighborhood)
    (z : U) (v : Intrinsic.FamilyFrames.FamilyChartTangent C) :
    F.centralTorusFamilyMap U hU (z, QuotientAddGroup.mk v) =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (Intrinsic.FamilyFrames.familyChartParameter C z))
        (F.transportedExponential z v).toMul := rfl

end

section

/-! The fixed central torus maps jointly continuously to the actual
total family on a constructed open neighborhood of the original point. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold ContDiff _root_.Topology

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

local instance IntrinsicFrame.TorusMap.nativeFrameTorusContinuity_nativeRealLieGroup (z : Intrinsic.FamilyFrames.FamilyChartBase C) [IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left] :
    LieGroup (𝓘(ℝ, Intrinsic.FamilyFrames.FamilyChartModel C z)) ∞ (Intrinsic.FamilyFrames.FamilyChartPoints C z) :=
  ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberLieGroup.Abelian.nativeScheme_realLieGroup (Intrinsic.FamilyFrames.familyChartFiber C z).scheme

variable (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.transportedExponential_apply (z : Intrinsic.FamilyFrames.FamilyChartBase C) (v : Intrinsic.FamilyFrames.FamilyChartTangent C) :
    let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C w).scheme.left := F.integral
    let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C w) := F.t2
    (F.transportedExponential z v).toMul =
      ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (G := Intrinsic.FamilyFrames.FamilyChartPoints C z) (E := Intrinsic.FamilyFrames.FamilyChartModel C z)
        (F.charts z) (F.realTransport z v) := rfl

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.centralTorusFamilyMap_continuous
    (U : Set (Intrinsic.FamilyFrames.FamilyChartBase C)) (hU : U ⊆ F.neighborhood) :
    let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left := F.integral
    let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C z) := F.t2
    ContinuousOn (fun z : Intrinsic.FamilyFrames.FamilyChartBase C × Intrinsic.FamilyFrames.FamilyChartTangent C =>
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (Intrinsic.FamilyFrames.familyChartParameter C z.1))
        (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (G := Intrinsic.FamilyFrames.FamilyChartPoints C z.1) (E := Intrinsic.FamilyFrames.FamilyChartModel C z.1)
          (F.charts z.1) z.2)) (U ×ˢ Set.univ) →
      Continuous (F.centralTorusFamilyMap U hU) := by
  let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left := F.integral
  let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C z) := F.t2
  dsimp only
  intro hφ
  apply ParametrizedQuotient.parametrizedQuotientMap_continuous F.centralLattice.toAddSubgroup
    (fun z : U => F.transportedExponential z)
    (fun z : U => F.transportedExponential_kernel z (hU z.property))
    (fun z : U => fun y : Additive (Intrinsic.FamilyFrames.FamilyChartPoints C z) =>
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (Intrinsic.FamilyFrames.familyChartParameter C z)) y.toMul)
  have hr : Continuous (fun z : U => (F.realTransport z).toContinuousLinearMap) :=
    (F.realTransport_continuous.mono hU).domRestrict
  have hv : Continuous (fun p : U × Intrinsic.FamilyFrames.FamilyChartTangent C => F.realTransport p.1 p.2) :=
    (hr.comp continuous_fst).clm_apply continuous_snd
  have harg : Continuous (fun p : U × Intrinsic.FamilyFrames.FamilyChartTangent C =>
      (p.1.val, F.realTransport p.1 p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk hv
  have h := hφ.comp_continuous harg (fun p => ⟨p.1.property, Set.mem_univ _⟩)
  apply h.congr
  intro p
  exact congrArg (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
    (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (Intrinsic.FamilyFrames.familyChartParameter C p.1)))
      (F.transportedExponential_apply p.1 p.2).symm

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.exists_continuous_centralTorusFamily
    (present : ∀ y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback y.left)) :
    ∃ (U : Set (Intrinsic.FamilyFrames.FamilyChartBase C)) (hU : U ⊆ F.neighborhood),
      IsOpen U ∧ Intrinsic.FamilyFrames.familyChartCenter C ∈ U ∧ Continuous (F.centralTorusFamilyMap U hU) := by
  obtain ⟨U, hUopen, hxU, hU, hφ⟩ := F.continuous_exponential present
  exact ⟨U, hU, hUopen, hxU, F.centralTorusFamilyMap_continuous U hU hφ⟩

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.centralTorusFamilyMap_center
    (U : Set (Intrinsic.FamilyFrames.FamilyChartBase C)) (hU : U ⊆ F.neighborhood) (hx : Intrinsic.FamilyFrames.familyChartCenter C ∈ U)
    (present : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (t : F.CentralTorus) :
    F.centralTorusFamilyMap U hU (⟨Intrinsic.FamilyFrames.familyChartCenter C, hx⟩, t) =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
        (F.centralTorusHomeomorph present t) := by
  let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left := F.integral
  let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C z) := F.t2
  induction t using Quotient.inductionOn with
  | h v =>
    rw [Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.centralTorusFamilyMap_mk, Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.centralTorusHomeomorph_mk]
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map _
      (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (G := Intrinsic.FamilyFrames.FamilyChartPoints C (Intrinsic.FamilyFrames.familyChartCenter C))
        (E := Intrinsic.FamilyFrames.FamilyChartModel C (Intrinsic.FamilyFrames.familyChartCenter C)) (F.charts (Intrinsic.FamilyFrames.familyChartCenter C))
        (F.realTransport (Intrinsic.FamilyFrames.familyChartCenter C) v)) = _
    rw [Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.realTransport_central]

end

section

/-! The fixed central torus maps continuously to each actual nearby
fiber through the same real period transport used in the total family. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold ContDiff _root_.Topology

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

local instance IntrinsicFrame.TorusMap.nativeFrameFiberMap_nativeRealLieGroup (z : Intrinsic.FamilyFrames.FamilyChartBase C)
    [IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left] :
    LieGroup (𝓘(ℝ, Intrinsic.FamilyFrames.FamilyChartModel C z)) ∞ (Intrinsic.FamilyFrames.FamilyChartPoints C z) :=
  ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberLieGroup.Abelian.nativeScheme_realLieGroup (Intrinsic.FamilyFrames.familyChartFiber C z).scheme

variable (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

def Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.torusFiberHom (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood) :
    F.CentralTorus →+ Additive (Intrinsic.FamilyFrames.FamilyChartPoints C z) :=
  QuotientAddGroup.lift F.centralLattice.toAddSubgroup
    (F.transportedExponential z) (F.transportedExponential_kernel z hz)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.torusFiberHom_mk (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (v : Intrinsic.FamilyFrames.FamilyChartTangent C) :
    F.torusFiberHom z hz (QuotientAddGroup.mk v) = F.transportedExponential z v := rfl

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.torusFiberHom_continuous (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood) :
    Continuous (fun v => (F.torusFiberHom z hz v).toMul) := by
  let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C w).scheme.left := F.integral
  let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C w) := F.t2
  apply QuotientAddGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff.mpr
  exact (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential_mdifferentiable (G := Intrinsic.FamilyFrames.FamilyChartPoints C z)
    (E := Intrinsic.FamilyFrames.FamilyChartModel C z) (F.charts z)).continuous.comp (F.realTransport z).continuous

def Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.torusFiberMap (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood) :
    C(F.CentralTorus, Intrinsic.FamilyFrames.FamilyChartPoints C z) :=
  ⟨fun v => (F.torusFiberHom z hz v).toMul, F.torusFiberHom_continuous z hz⟩

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.torusFiberMap_family (U : Set (Intrinsic.FamilyFrames.FamilyChartBase C)) (hU : U ⊆ F.neighborhood)
    (z : U) (v : F.CentralTorus) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (Intrinsic.FamilyFrames.familyChartParameter C z))
      (F.torusFiberMap z (hU z.property) v) = F.centralTorusFamilyMap U hU (z, v) := rfl

end

/-! The original presentation of each actual fiber preserves the exact
map from the fixed central torus and its inclusion into the total family. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

variable (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

def Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberInclusion (z : Intrinsic.FamilyFrames.FamilyChartBase C)
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z)) : P.variety.toOver ⟶ ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G :=
  P.comparison.inv ≫ ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (Intrinsic.FamilyFrames.familyChartParameter C z)

def Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedTorusMap (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z)) :
    C(F.CentralTorus, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.variety.toOver) :=
  (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous P.comparison.hom).comp (F.torusFiberMap z hz)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedTorusMap_family (U : Set (Intrinsic.FamilyFrames.FamilyChartBase C)) (hU : U ⊆ F.neighborhood)
    (z : U) (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z)) (v : F.CentralTorus) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberInclusion (C := C) z P)
      (F.presentedTorusMap z (hU z.property) P v) = F.centralTorusFamilyMap U hU (z, v) := by
  change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (P.comparison.inv ≫ _)
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.comparison.hom (F.torusFiberMap z (hU z.property) v)) = _
  rw [← AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact F.torusFiberMap_family U hU z v

end

end OAI.RepresentationTheory.Theta.Geometric
