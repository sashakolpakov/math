import OAI.AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris
import OAI.AlgebraicGeometry.CycleClass.Geometric.SphereCover
import OAI.AlgebraicGeometry.CycleClass.Geometric.ZeroSphere
import OAI.AlgebraicGeometry.CycleClass.Geometric.HomologyZeroNaturality

/-! # Small Circle Homology -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SmallCircleHomology.Cycles

noncomputable section

/-!
# Homology of the actual two-chart small singular chains on a circle

The complex in this file consists of genuine singular simplices whose images
lie in one of the two stereographic charts. No assertion that its inclusion
in all singular chains is a quasi-isomorphism is used here.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

abbrev standardCircle : TopCat.{0} :=
  TopCat.of (NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin 2)))

abbrev circleFirstChart : Set standardCircle := SphereCover.Cycles.spherePoleOpen (SphereCover.Cycles.standardSphereNorthPole 1)
abbrev circleSecondChart : Set standardCircle := SphereCover.Cycles.spherePoleOpen (-SphereCover.Cycles.standardSphereNorthPole 1)
abbrev circleOverlap : TopCat.{0} :=
  TopCat.of (circleFirstChart ∩ circleSecondChart : Set standardCircle)

abbrev smallCircleChains : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  SmallMayerVietoris.Cycles.binarySmallSingularChains standardCircle circleFirstChart circleSecondChart

abbrev smallCircleHomology (n : ℕ) : ModuleCat.{0} ℤ := smallCircleChains.homology n

/-- The real one-dimensional Euclidean sphere is the unit sphere in `ℝ`. -/
def euclideanLineSphereHomeomorph :
    NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin 1)) ≃ₜ ZeroSphere.Cycles.realZeroSphere :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm.toHomeomorph.subtype (fun x ↦ by
    simp only [NormalSphere.Cycles.NormalUnitSphere, Metric.mem_sphere, dist_zero_right]
    change ‖x‖ = 1 ↔ ‖(OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm x‖ = 1
    rw [LinearIsometryEquiv.norm_map]
    rfl)

/-- The overlap of the specified circle charts has the homotopy type of the
specified two-point zero-sphere. -/
def circleOverlapZeroSphereEquiv : ContinuousMap.HomotopyEquiv circleOverlap ZeroSphere.Cycles.zeroSphere :=
  ((SphereCover.Cycles.standardSphereOverlapEquiv 1).trans euclideanLineSphereHomeomorph.toHomotopyEquiv).trans
    ZeroSphere.Cycles.zeroSphereRealHomeomorph.symm.toHomotopyEquiv

/-- The actual homology equivalence induced by the explicit overlap contraction. -/
def circleOverlapHomologyIso (n : ℕ) :
    RelativeHomologyExact.Cycles.integralSingularHomology circleOverlap n ≅ RelativeHomologyExact.Cycles.integralSingularHomology ZeroSphere.Cycles.zeroSphere n :=
  ContractibleModel.Cycles.singularHomologyIsoOfHomotopyEquiv (ModuleCat.of ℤ ℤ) circleOverlapZeroSphereEquiv n

theorem circleOverlap_higherHomology_isZero (n : ℕ) (hn : n ≠ 0) :
    IsZero (RelativeHomologyExact.Cycles.integralSingularHomology circleOverlap n) :=
  (ZeroSphere.Cycles.zeroSphere_higherHomology_isZero n hn).of_iso (circleOverlapHomologyIso n)

/-- Both actual chart homologies vanish in positive degrees. -/
theorem smallCircleMiddle_higherHomology_isZero (n : ℕ) (hn : n ≠ 0) :
    IsZero ((SmallMayerVietoris.Cycles.smallMayerVietorisSequence standardCircle circleFirstChart circleSecondChart).X₂.homology n) := by
  have hu : IsZero (RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of circleFirstChart) n) := by
    let := SphereCover.Cycles.spherePoleOpen_contractible (SphereCover.Cycles.standardSphereNorthPole 1)
    exact ContractibleModel.Cycles.isZero_integralSingularHomology_of_contractible _ n hn
  have hv : IsZero (RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of circleSecondChart) n) := by
    let := SphereCover.Cycles.spherePoleOpen_contractible (-SphereCover.Cycles.standardSphereNorthPole 1)
    exact ContractibleModel.Cycles.isZero_integralSingularHomology_of_contractible _ n hn
  exact ((biprod_isZero_iff _ _).mpr ⟨hu, hv⟩).of_iso
    (SmallMayerVietoris.Cycles.smallMayerVietorisMiddleHomologyIso standardCircle circleFirstChart circleSecondChart n)

/-- The actual connecting map for the two circle charts. -/
abbrev smallCircleBoundary (n : ℕ) :
    smallCircleHomology (n + 1) ⟶ RelativeHomologyExact.Cycles.integralSingularHomology circleOverlap n :=
  SmallMayerVietoris.Cycles.smallMayerVietorisBoundary standardCircle circleFirstChart circleSecondChart n

/-- Above degree one, the actual connecting map is an isomorphism. -/
def smallCircleBoundaryIso (n : ℕ) (hn : n ≠ 0) :
    smallCircleHomology (n + 1) ≅ RelativeHomologyExact.Cycles.integralSingularHomology circleOverlap n :=
  (SmallMayerVietoris.Cycles.smallMayerVietorisSequence_shortExact standardCircle circleFirstChart circleSecondChart).δIso
    (n + 1) n rfl
    (smallCircleMiddle_higherHomology_isZero (n + 1) (Nat.succ_ne_zero n))
    (smallCircleMiddle_higherHomology_isZero n hn)

/-- The actual small-chain circle complex has zero homology above degree one. -/
theorem smallCircle_higherHomology_isZero (n : ℕ) (hn : n ≠ 0) :
    IsZero (smallCircleHomology (n + 1)) :=
  (circleOverlap_higherHomology_isZero n hn).of_iso (smallCircleBoundaryIso n hn)

/-- The circle connecting map is injective in degree one because both chart
homologies vanish in degree one. -/
theorem smallCircleBoundary_zero_injective : Function.Injective (smallCircleBoundary 0).hom := by
  apply LinearMap.ker_eq_bot.mp
  rw [← SmallMayerVietoris.Cycles.smallMayerVietoris_range_middle standardCircle circleFirstChart circleSecondChart 0]
  have hzero := (smallCircleMiddle_higherHomology_isZero 1 (by decide)).eq_zero_of_src
    (HomologicalComplex.homologyMap
      (SmallMayerVietoris.Cycles.smallMayerVietorisSequence standardCircle circleFirstChart circleSecondChart).g 1)
  rw [hzero]
  exact LinearMap.range_zero

/-- The actual overlap-to-chart-sum map on degree-zero homology. -/
abbrev circleH0InclusionMap : RelativeHomologyExact.Cycles.integralSingularHomology circleOverlap 0 →ₗ[ℤ]
    (SmallMayerVietoris.Cycles.smallMayerVietorisSequence standardCircle circleFirstChart circleSecondChart).X₂.homology 0 :=
  (HomologicalComplex.homologyMap
    (SmallMayerVietoris.Cycles.smallMayerVietorisSequence standardCircle circleFirstChart circleSecondChart).f 0).hom

abbrev circleH0Kernel := LinearMap.ker circleH0InclusionMap

/-- Degree-one small-chain circle homology identifies with the actual kernel
of the inclusion map from overlap H₀ to the two chart H₀ groups. -/
def smallCircleH1KernelEquiv : smallCircleHomology 1 ≃+ circleH0Kernel := by
  let f : smallCircleHomology 1 →+ circleH0Kernel :=
    { toFun := fun x ↦ ⟨(smallCircleBoundary 0).hom x, by
        have h : (smallCircleBoundary 0).hom x ∈ LinearMap.range (smallCircleBoundary 0).hom :=
          ⟨x, rfl⟩
        rw [SmallMayerVietoris.Cycles.smallMayerVietoris_range_boundary standardCircle circleFirstChart circleSecondChart 0] at h
        exact h⟩
      map_zero' := Subtype.ext (map_zero (smallCircleBoundary 0).hom)
      map_add' := fun x y ↦ Subtype.ext (map_add (smallCircleBoundary 0).hom x y) }
  refine AddEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    exact smallCircleBoundary_zero_injective (congrArg Subtype.val h)
  · intro y
    have hy : (y : RelativeHomologyExact.Cycles.integralSingularHomology circleOverlap 0) ∈
        LinearMap.range (smallCircleBoundary 0).hom := by
      rw [SmallMayerVietoris.Cycles.smallMayerVietoris_range_boundary standardCircle circleFirstChart circleSecondChart 0]
      exact y.property
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩

/-- The augmentation kernel on the zero-sphere is canonically the integers,
with coefficient measured at its first labelled point. -/
def zeroSphereAugmentationKernelEquiv :
    LinearMap.ker ZeroSphere.Cycles.zeroSphereAugmentation.hom ≃+ ℤ where
  toFun x := ZeroSphere.Cycles.zeroSphereCoordinates x.val 0
  invFun n := ⟨n • ZeroSphere.Cycles.zeroSphereDifferenceClass, by
    change ZeroSphere.Cycles.zeroSphereAugmentation.hom (n • ZeroSphere.Cycles.zeroSphereDifferenceClass) = 0
    rw [map_zsmul]
    change n • (ZeroSphere.Cycles.zeroSphereAugmentation ZeroSphere.Cycles.zeroSphereDifferenceClass) = 0
    rw [ZeroSphere.Cycles.zeroSphereDifferenceClass_augmentation, smul_zero]⟩
  left_inv x := by
    obtain ⟨n, hn, _⟩ := ZeroSphere.Cycles.zeroSphereAugmentation_kernel_generator x.val x.property
    have hc := congrArg (fun y ↦ ZeroSphere.Cycles.zeroSphereCoordinates y 0) hn
    rw [ZeroSphere.Cycles.zeroSphereCoordinates_zsmul, ZeroSphere.Cycles.zeroSphereDifferenceClass_coordinates] at hc
    have hc' : n = ZeroSphere.Cycles.zeroSphereCoordinates x.val 0 := by simpa using hc
    apply Subtype.ext
    change ZeroSphere.Cycles.zeroSphereCoordinates x.val 0 • ZeroSphere.Cycles.zeroSphereDifferenceClass = x.val
    rw [← hc']
    exact hn
  right_inv n := by
    change ZeroSphere.Cycles.zeroSphereCoordinates (n • ZeroSphere.Cycles.zeroSphereDifferenceClass) 0 = n
    rw [ZeroSphere.Cycles.zeroSphereCoordinates_zsmul, ZeroSphere.Cycles.zeroSphereDifferenceClass_coordinates]
    simp
  map_add' x y := by
    change ZeroSphere.Cycles.zeroSphereCoordinates (x.val + y.val) 0 = _
    simp

/-- The canonical augmentation is an isomorphism on the first contractible chart. -/
def circleFirstChartH0Iso :
    RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of circleFirstChart) 0 ≅ ModuleCat.of ℤ ℤ := by
  let := SphereCover.Cycles.spherePoleOpen_contractible (SphereCover.Cycles.standardSphereNorthPole 1)
  exact ContractibleModel.Cycles.integralSingularH0Iso _

/-- The canonical augmentation is an isomorphism on the second contractible chart. -/
def circleSecondChartH0Iso :
    RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of circleSecondChart) 0 ≅ ModuleCat.of ℤ ℤ := by
  let := SphereCover.Cycles.spherePoleOpen_contractible (-SphereCover.Cycles.standardSphereNorthPole 1)
  exact ContractibleModel.Cycles.integralSingularH0Iso _

def circleOverlapAugmentation : RelativeHomologyExact.Cycles.integralSingularHomology circleOverlap 0 ⟶ ModuleCat.of ℤ ℤ := by
  let f := circleOverlap.singularHomology₀ε (C := ModuleCat.{0} ℤ) (ModuleCat.of ℤ ℤ)
  exact f

abbrev circleFirstH0Inclusion : RelativeHomologyExact.Cycles.integralSingularHomology circleOverlap 0 ⟶
    RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of circleFirstChart) 0 :=
  RelativeHomologyExact.Cycles.integralSingularHomologyMap (SmallMayerVietoris.Cycles.subsetInclusion standardCircle
    (Set.inter_subset_left : circleFirstChart ∩ circleSecondChart ⊆ circleFirstChart)) 0

abbrev circleSecondH0Inclusion : RelativeHomologyExact.Cycles.integralSingularHomology circleOverlap 0 ⟶
    RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of circleSecondChart) 0 :=
  RelativeHomologyExact.Cycles.integralSingularHomologyMap (SmallMayerVietoris.Cycles.subsetInclusion standardCircle
    (Set.inter_subset_right : circleFirstChart ∩ circleSecondChart ⊆ circleSecondChart)) 0

theorem circleFirstH0Inclusion_augmentation :
    circleFirstH0Inclusion ≫ circleFirstChartH0Iso.hom = circleOverlapAugmentation :=
  HomologyZeroNaturality.Cycles.integralSingularH0_augmentation_naturality _

theorem circleSecondH0Inclusion_augmentation :
    circleSecondH0Inclusion ≫ circleSecondChartH0Iso.hom = circleOverlapAugmentation :=
  HomologyZeroNaturality.Cycles.integralSingularH0_augmentation_naturality _

theorem circleOverlapHomologyIso_augmentation :
    (circleOverlapHomologyIso 0).hom ≫ ZeroSphere.Cycles.zeroSphereAugmentation = circleOverlapAugmentation :=
  HomologyZeroNaturality.Cycles.singularH0_augmentation_homotopyEquiv circleOverlapZeroSphereEquiv (ModuleCat.of ℤ ℤ)

theorem moduleBiprod_eq_zero_iff (A B : ModuleCat.{0} ℤ) (x : (A ⊞ B : ModuleCat.{0} ℤ)) :
    x = 0 ↔ (biprod.fst : A ⊞ B ⟶ A) x = 0 ∧ (biprod.snd : A ⊞ B ⟶ B) x = 0 := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h₁, h₂⟩
    have h := congrArg (fun f : A ⊞ B ⟶ A ⊞ B ↦ f x) (biprod.total (X := A) (Y := B))
    change (biprod.inl : A ⟶ A ⊞ B) ((biprod.fst : A ⊞ B ⟶ A) x) +
      (biprod.inr : B ⟶ A ⊞ B) ((biprod.snd : A ⊞ B ⟶ B) x) = x at h
    rw [h₁, h₂, map_zero, map_zero, zero_add] at h
    exact h.symm

set_option backward.isDefEq.respectTransparency false in
theorem circleH0Inclusion_zero_iff (x : RelativeHomologyExact.Cycles.integralSingularHomology circleOverlap 0) :
    circleH0InclusionMap x = 0 ↔ circleFirstH0Inclusion x = 0 ∧ circleSecondH0Inclusion x = 0 := by
  let e := SmallMayerVietoris.Cycles.smallMayerVietorisMiddleHomologyIso standardCircle circleFirstChart circleSecondChart 0
  have he : e.hom (circleH0InclusionMap x) = 0 ↔ circleH0InclusionMap x = 0 :=
    e.toLinearEquiv.map_eq_zero_iff
  rw [← he, moduleBiprod_eq_zero_iff]
  have h₁ := congrArg (fun f ↦ f x)
    (SmallMayerVietoris.Cycles.smallMayerVietoris_homology_f_fst standardCircle circleFirstChart circleSecondChart 0)
  have h₂ := congrArg (fun f ↦ f x)
    (SmallMayerVietoris.Cycles.smallMayerVietoris_homology_f_snd standardCircle circleFirstChart circleSecondChart 0)
  change (biprod.fst :
    RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of circleFirstChart) 0 ⊞
      RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of circleSecondChart) 0 ⟶
        RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of circleFirstChart) 0)
    (e.hom (circleH0InclusionMap x)) = circleFirstH0Inclusion x at h₁
  change (biprod.snd :
    RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of circleFirstChart) 0 ⊞
      RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of circleSecondChart) 0 ⟶
        RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of circleSecondChart) 0)
    (e.hom (circleH0InclusionMap x)) = -circleSecondH0Inclusion x at h₂
  rw [h₁, h₂, neg_eq_zero]

theorem circleH0Kernel_augmentation_iff (x : RelativeHomologyExact.Cycles.integralSingularHomology circleOverlap 0) :
    circleH0InclusionMap x = 0 ↔ circleOverlapAugmentation x = 0 := by
  rw [circleH0Inclusion_zero_iff]
  have h₁ := congrArg (fun f ↦ f x) circleFirstH0Inclusion_augmentation
  have h₂ := congrArg (fun f ↦ f x) circleSecondH0Inclusion_augmentation
  change circleFirstChartH0Iso.hom (circleFirstH0Inclusion x) = circleOverlapAugmentation x at h₁
  change circleSecondChartH0Iso.hom (circleSecondH0Inclusion x) = circleOverlapAugmentation x at h₂
  constructor
  · rintro ⟨hu, _⟩
    rw [hu, map_zero] at h₁
    exact h₁.symm
  · intro h
    constructor
    · apply (ConcreteCategory.bijective_of_isIso circleFirstChartH0Iso.hom).1
      simpa only [map_zero, h] using h₁
    · apply (ConcreteCategory.bijective_of_isIso circleSecondChartH0Iso.hom).1
      simpa only [map_zero, h] using h₂

def circleOverlapH0Equiv : RelativeHomologyExact.Cycles.integralSingularHomology circleOverlap 0 ≃ₗ[ℤ] ZeroSphere.Cycles.zeroSphereH0 :=
  (circleOverlapHomologyIso 0).toLinearEquiv

theorem circleH0Kernel_zeroSphere_iff (x : RelativeHomologyExact.Cycles.integralSingularHomology circleOverlap 0) :
    circleH0InclusionMap x = 0 ↔ ZeroSphere.Cycles.zeroSphereAugmentation (circleOverlapH0Equiv x) = 0 := by
  have h := congrArg (fun f ↦ f x) circleOverlapHomologyIso_augmentation
  change ZeroSphere.Cycles.zeroSphereAugmentation (circleOverlapH0Equiv x) = circleOverlapAugmentation x at h
  rw [h]
  exact circleH0Kernel_augmentation_iff x

/-- The actual Mayer–Vietoris overlap kernel is the computed augmentation
kernel of the specified zero-sphere. -/
def circleH0KernelZeroSphereEquiv : circleH0Kernel ≃+ LinearMap.ker ZeroSphere.Cycles.zeroSphereAugmentation.hom where
  toFun x := ⟨circleOverlapH0Equiv x.val, (circleH0Kernel_zeroSphere_iff x.val).mp x.property⟩
  invFun x := ⟨circleOverlapH0Equiv.symm x.val, by
    apply (circleH0Kernel_zeroSphere_iff _).mpr
    rw [circleOverlapH0Equiv.apply_symm_apply]
    exact x.property⟩
  left_inv x := Subtype.ext (circleOverlapH0Equiv.symm_apply_apply x.val)
  right_inv x := Subtype.ext (circleOverlapH0Equiv.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (circleOverlapH0Equiv.map_add x.val y.val)

/-- The actual degree-one homology of the two-chart small circle complex is
the integer module. Its sign is fixed by the given overlap equivalence and
the difference of the labelled zero-sphere point classes. -/
def smallCircleH1Equiv : smallCircleHomology 1 ≃ₗ[ℤ] ℤ :=
  ((smallCircleH1KernelEquiv.trans circleH0KernelZeroSphereEquiv).trans
    zeroSphereAugmentationKernelEquiv).toIntLinearEquiv

def smallCircleH1Iso : smallCircleHomology 1 ≅ ModuleCat.of ℤ ℤ :=
  smallCircleH1Equiv.toModuleIso

/-- The generator normalized by the actual Mayer–Vietoris connecting map. -/
def smallCircleGenerator : smallCircleHomology 1 := smallCircleH1Equiv.symm 1

@[simp]
theorem smallCircleGenerator_normalization : smallCircleH1Equiv smallCircleGenerator = 1 :=
  smallCircleH1Equiv.apply_symm_apply 1

theorem smallCircleGenerator_ne_zero : smallCircleGenerator ≠ 0 := by
  intro h
  have hn := smallCircleGenerator_normalization
  rw [h, map_zero] at hn
  exact zero_ne_one hn

/-- Under the actual connecting map and the specified overlap equivalence,
the generator has boundary equal to the oriented difference of the two points. -/
theorem smallCircleGenerator_boundary :
    circleOverlapH0Equiv ((smallCircleBoundary 0).hom smallCircleGenerator) =
      ZeroSphere.Cycles.zeroSphereDifferenceClass := by
  let k := circleH0KernelZeroSphereEquiv (smallCircleH1KernelEquiv smallCircleGenerator)
  have hk : zeroSphereAugmentationKernelEquiv k = 1 := smallCircleGenerator_normalization
  have hk' : k = zeroSphereAugmentationKernelEquiv.symm 1 := by
    simpa using congrArg zeroSphereAugmentationKernelEquiv.symm hk
  have hval := congrArg Subtype.val hk'
  change circleOverlapH0Equiv ((smallCircleBoundary 0).hom smallCircleGenerator) =
    (1 : ℤ) • ZeroSphere.Cycles.zeroSphereDifferenceClass at hval
  simpa using hval

/-- Every small-chain circle class is a unique integer multiple of the
connecting-map-normalized generator. -/
theorem smallCircleGenerator_generates (x : smallCircleHomology 1) :
    ∃! n : ℤ, n • smallCircleGenerator = x := by
  have hnorm (n : ℤ) : smallCircleH1Equiv (n • smallCircleGenerator) = n := by
    calc
      smallCircleH1Equiv (n • smallCircleGenerator) =
          n • smallCircleH1Equiv smallCircleGenerator :=
        map_zsmul smallCircleH1Equiv.toLinearMap _ _
      _ = n := by rw [smallCircleGenerator_normalization]; simp
  refine ⟨smallCircleH1Equiv x, ?_, ?_⟩
  · apply smallCircleH1Equiv.injective
    exact hnorm _
  · intro n hn
    calc
      n = smallCircleH1Equiv (n • smallCircleGenerator) := (hnorm n).symm
      _ = smallCircleH1Equiv x := congrArg smallCircleH1Equiv hn

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SmallCircleHomology.Cycles
