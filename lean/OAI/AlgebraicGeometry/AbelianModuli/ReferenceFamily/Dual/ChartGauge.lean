import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.TransitionCocycle
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.GaugeNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.Gauge

/-! # Chart Gauge -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGauge

noncomputable section

section

/-! A zero-cochain of derivations on the actual affine cover supplies
normalized adjusted product charts on each affine subopen of that cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] CommonOpenFiber.dualCommonOpenFiber CommonOpenFiber.dualAffineCommonOpenFiber
attribute [local implicit_reducible] NormalizedDual.OpenProductData.NormalizesProductFiber
attribute [local irreducible] Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso DualOpen.CommonTransitions.affineChartProductOnOpen

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k)))) (U : X.left.AffineOpenCover)

def dualFamilyChartAffineOpen (i : U.I₀) : X.left.affineOpens :=
  ⟨(U.f i).opensRange, isAffineOpen_opensRange (U.f i)⟩

def dualChartGaugeParameters := ∀ i : U.I₀,
  Derivation k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X (dualFamilyChartAffineOpen k X U i)))
    (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X (dualFamilyChartAffineOpen k X U i)))

attribute [local implicit_reducible] dualFamilyChartAffineOpen dualChartGaugeParameters

variable [Smooth X.hom] (a : dualChartGaugeParameters k X U) (V : X.left.affineOpens)

def dualChartGaugeCoefficient (i : U.I₀) (hi : V.1 ≤ (U.f i).opensRange) :
    Derivation k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X V))
      (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X V)) :=
  CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction k X
    (show V.1 ≤ (dualFamilyChartAffineOpen k X U i).1 from hi) (a i)

def dualChartGaugeOnOpen (i : U.I₀) (hi : V.1 ≤ (U.f i).opensRange) :
    OpenChart.dualFamilyOpenObject k X V.1 ≅ (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)).obj (CommonOpenFiber.dualAffineCommonOpenFiber k X V) :=
  (DualOpen.CommonTransitions.affineChartProductOnOpen k X U i V.1 hi).iso ≪≫
    AffineProduct.ChartGaugeCancellation.affineProductDerivationGauge k (CommonOpenFiber.dualAffineCommonOpenFiber k X V) (dualChartGaugeCoefficient k X U a V i hi)

theorem dualChartGaugeOnOpen_normalized (i : U.I₀) (hi : V.1 ≤ (U.f i).opensRange) :
    NormalizedDual.OpenProductData.NormalizesDualProductFiber k (dualChartGaugeOnOpen k X U a V i hi) :=
  NormalizedProduct.Gauge.normalizesProductFiber_postcomp (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)) (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k))
    (Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso k) (DualOpen.CommonTransitions.affineChartProductOnOpen k X U i V.1 hi).iso
    (DualOpen.CommonTransitions.affineChartProductOnOpen k X U i V.1 hi).normalized
    (AffineProduct.ChartGaugeCancellation.affineProductDerivationGauge k (CommonOpenFiber.dualAffineCommonOpenFiber k X V) (dualChartGaugeCoefficient k X U a V i hi))
    (AffineProduct.ChartGaugeCancellation.affineProductDerivationGauge_fiberIdentity k (CommonOpenFiber.dualAffineCommonOpenFiber k X V)
      (dualChartGaugeCoefficient k X U a V i hi))

end

section

/-! The chart adjustments obtained from a zero-cochain commute with
actual open restriction, including successive coefficient restrictions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] CommonOpenFiber.dualCommonOpenFiber CommonOpenFiber.dualAffineCommonOpenFiber CommonOpenCoefficientRestriction.dualAffineCommonOpenMap
attribute [local implicit_reducible] dualFamilyChartAffineOpen dualChartGaugeParameters
attribute [local irreducible] DualOpen.CommonTransitions.affineChartProductOnOpen Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k))))
    (U : X.left.AffineOpenCover) (a : dualChartGaugeParameters k X U)
    {V W : X.left.affineOpens} (h : V.1 ≤ W.1)

theorem dualChartGaugeCoefficient_restrict (i : U.I₀) (hi : W.1 ≤ (U.f i).opensRange) :
    CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction k X h (dualChartGaugeCoefficient k X U a W i hi) =
      dualChartGaugeCoefficient k X U a V i (h.trans hi) :=
  LinearMap.congr_fun (AffineDerivationPresheaf.dualCommonOpenDerivationRestriction_comp k X h
    (show W.1 ≤ (dualFamilyChartAffineOpen k X U i).1 from hi)) (a i)

theorem dualChartGaugeCoefficient_natural (i : U.I₀) (hi : W.1 ≤ (U.f i).opensRange)
    (c : HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X W)) :
    CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap k X h (dualChartGaugeCoefficient k X U a W i hi c) =
      dualChartGaugeCoefficient k X U a V i (h.trans hi) (CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap k X h c) := by
  have hm := EtaleHomDerivation.etaleAlgHomDerivationLinear_map (CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap k X h)
    (CommonOpenDerivationExtension.dualAffineCommonOpenAlgebraMap_etale k X h) (dualChartGaugeCoefficient k X U a W i hi) c
  exact hm.symm.trans (Derivation.congr_fun (dualChartGaugeCoefficient_restrict k X U a h i hi)
    (CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap k X h c))

variable [Smooth X.hom]

theorem dualChartGaugeOnOpen_restriction (i : U.I₀) (hi : W.1 ≤ (U.f i).opensRange) :
    (dualChartGaugeOnOpen k X U a V i (h.trans hi)).hom ≫
        (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)).map (CommonOpenCoefficientRestriction.dualAffineCommonOpenMap k X h) =
      OpenChart.dualFamilyOpenMap k X h ≫ (dualChartGaugeOnOpen k X U a W i hi).hom := by
  have hg := AffineProduct.GaugeNaturality.affineProductDerivationGauge_natural k
    (X := CommonOpenFiber.dualAffineCommonOpenFiber k X V) (Y := CommonOpenFiber.dualAffineCommonOpenFiber k X W)
    (CommonOpenCoefficientRestriction.dualAffineCommonOpenMap k X h)
    (dualChartGaugeCoefficient k X U a V i (h.trans hi)) (dualChartGaugeCoefficient k X U a W i hi)
    (dualChartGaugeCoefficient_natural k X U a h i hi)
  exact NormalizedProduct.Gauge.productChartGauge_restriction_square (OpenChart.dualFamilyOpenMap k X h)
    ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)).map (CommonOpenCoefficientRestriction.dualAffineCommonOpenMap k X h))
    (DualOpen.CommonTransitions.affineChartProductOnOpen k X U i V.1 (h.trans hi)).iso (DualOpen.CommonTransitions.affineChartProductOnOpen k X U i W.1 hi).iso
    (AffineProduct.ChartGaugeCancellation.affineProductDerivationGauge k (CommonOpenFiber.dualAffineCommonOpenFiber k X V) (dualChartGaugeCoefficient k X U a V i (h.trans hi)))
    (AffineProduct.ChartGaugeCancellation.affineProductDerivationGauge k (CommonOpenFiber.dualAffineCommonOpenFiber k X W) (dualChartGaugeCoefficient k X U a W i hi))
    (CommonOpenRestriction.affineChartProductOnOpen_restriction k X U h i hi) hg

end

/-! The first two Cech differentials of the actual affine derivation
presheaf, written on the literal pair and triple intersections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] CommonOpenCocycle.dualFamilyPairAffineOpen CommonOpenCocycle.dualFamilyTripleAffineOpen
attribute [local implicit_reducible] dualChartGaugeParameters dualFamilyChartAffineOpen

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k))))
    (U : X.left.AffineOpenCover)

instance dualChartGaugeParameters_addCommGroup : AddCommGroup (dualChartGaugeParameters k X U) :=
  inferInstanceAs (AddCommGroup (∀ i : U.I₀,
    Derivation k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X (dualFamilyChartAffineOpen k X U i)))
      (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X (dualFamilyChartAffineOpen k X U i)))))

instance dualChartGaugeParameters_module : Module k (dualChartGaugeParameters k X U) :=
  inferInstanceAs (Module k (∀ i : U.I₀,
    Derivation k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X (dualFamilyChartAffineOpen k X U i)))
      (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X (dualFamilyChartAffineOpen k X U i)))))

variable [IsSeparated X.hom]

abbrev dualAffineCechOneCochains := ∀ i j : U.I₀,
  Derivation k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X (CommonOpenCocycle.dualFamilyPairAffineOpen k X U i j)))
    (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X (CommonOpenCocycle.dualFamilyPairAffineOpen k X U i j)))

abbrev dualAffineCechTwoCochains := ∀ i j l : U.I₀,
  Derivation k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X (CommonOpenCocycle.dualFamilyTripleAffineOpen k X U i j l)))
    (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X (CommonOpenCocycle.dualFamilyTripleAffineOpen k X U i j l)))

def dualAffineCechDifferentialZero : dualChartGaugeParameters k X U →ₗ[k] dualAffineCechOneCochains k X U := by
  let ev (i : U.I₀) : dualChartGaugeParameters k X U →ₗ[k]
      Derivation k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X (dualFamilyChartAffineOpen k X U i)))
        (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X (dualFamilyChartAffineOpen k X U i))) :=
    LinearMap.proj i
  exact LinearMap.pi (fun i => LinearMap.pi (fun j =>
    (CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction k X
      (show (CommonOpenCocycle.dualFamilyPairAffineOpen k X U i j).1 ≤ (dualFamilyChartAffineOpen k X U i).1 from inf_le_left)).comp (ev i) -
    (CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction k X
      (show (CommonOpenCocycle.dualFamilyPairAffineOpen k X U i j).1 ≤ (dualFamilyChartAffineOpen k X U j).1 from inf_le_right)).comp (ev j)))

theorem dualAffineCechDifferentialZero_apply (a : dualChartGaugeParameters k X U) (i j : U.I₀) :
    dualAffineCechDifferentialZero k X U a i j =
      dualChartGaugeCoefficient k X U a (CommonOpenCocycle.dualFamilyPairAffineOpen k X U i j) i inf_le_left -
        dualChartGaugeCoefficient k X U a (CommonOpenCocycle.dualFamilyPairAffineOpen k X U i j) j inf_le_right := rfl

def dualAffineCechDifferentialOne : dualAffineCechOneCochains k X U →ₗ[k] dualAffineCechTwoCochains k X U where
  toFun a i j l :=
    CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction k X
        (show (CommonOpenCocycle.dualFamilyTripleAffineOpen k X U i j l).1 ≤ (CommonOpenCocycle.dualFamilyPairAffineOpen k X U i j).1 from
          inf_le_left) (a i j) +
      CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction k X
        (show (CommonOpenCocycle.dualFamilyTripleAffineOpen k X U i j l).1 ≤ (CommonOpenCocycle.dualFamilyPairAffineOpen k X U j l).1 from
          le_inf (inf_le_left.trans inf_le_right) inf_le_right) (a j l) -
      CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction k X
        (show (CommonOpenCocycle.dualFamilyTripleAffineOpen k X U i j l).1 ≤ (CommonOpenCocycle.dualFamilyPairAffineOpen k X U i l).1 from
          le_inf (inf_le_left.trans inf_le_left) inf_le_right) (a i l)
  map_add' a b := by
    funext i j l
    simp only [Pi.add_apply, map_add]
    abel
  map_smul' c a := by
    funext i j l
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_add, smul_sub]

theorem dualAffineCechDifferentialOne_apply (a : dualAffineCechOneCochains k X U) (i j l : U.I₀) :
    dualAffineCechDifferentialOne k X U a i j l =
      CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction k X
        (show (CommonOpenCocycle.dualFamilyTripleAffineOpen k X U i j l).1 ≤ (CommonOpenCocycle.dualFamilyPairAffineOpen k X U i j).1 from
          inf_le_left) (a i j) +
      CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction k X
        (show (CommonOpenCocycle.dualFamilyTripleAffineOpen k X U i j l).1 ≤ (CommonOpenCocycle.dualFamilyPairAffineOpen k X U j l).1 from
          le_inf (inf_le_left.trans inf_le_right) inf_le_right) (a j l) -
      CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction k X
        (show (CommonOpenCocycle.dualFamilyTripleAffineOpen k X U i j l).1 ≤ (CommonOpenCocycle.dualFamilyPairAffineOpen k X U i l).1 from
          le_inf (inf_le_left.trans inf_le_left) inf_le_right) (a i l) := rfl

theorem dualAffineCechDifferential_comp (a : dualChartGaugeParameters k X U) :
    dualAffineCechDifferentialOne k X U (dualAffineCechDifferentialZero k X U a) = 0 := by
  funext i j l
  simp only [Pi.zero_apply]
  rw [dualAffineCechDifferentialOne_apply, dualAffineCechDifferentialZero_apply,
    dualAffineCechDifferentialZero_apply, dualAffineCechDifferentialZero_apply]
  rw [map_sub, map_sub, map_sub]
  rw [dualChartGaugeCoefficient_restrict, dualChartGaugeCoefficient_restrict,
    dualChartGaugeCoefficient_restrict, dualChartGaugeCoefficient_restrict,
    dualChartGaugeCoefficient_restrict, dualChartGaugeCoefficient_restrict]
  abel

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGauge
