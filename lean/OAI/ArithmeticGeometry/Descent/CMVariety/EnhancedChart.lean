import OAI.ArithmeticGeometry.Descent.CMVariety.SmoothArithmetic
import OAI.ArithmeticGeometry.Descent.CMVariety.SmoothEnhancedTupleSpread

/-! # Enhanced Chart -/

namespace OAI

noncomputable section

namespace ArithmeticGeometry.Descent.CMVariety

/-! Transport actual enhanced fibers and their extra tuples into the
constructed injective arithmetic chart, and compare successive pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

def AbelianEndomorphism.AbelianEndomorphismTuple.conjugate
    {Index : Type} {g : ℕ} {S : Scheme} {A B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (k : AbelianEndomorphism.AbelianEndomorphismTuple Index B) (e : A.scheme ≅ B.scheme) (he : IsMonHom e.hom) :
    AbelianEndomorphism.AbelianEndomorphismTuple Index A where
  map i := e.hom ≫ k.map i ≫ e.inv
  group i := by
    let : IsMonHom e.hom := he
    infer_instance

theorem AbelianEndomorphism.AbelianEndomorphismTuple.conjugate_comparison
    {Index : Type} {g : ℕ} {S : Scheme} {A B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (k : AbelianEndomorphism.AbelianEndomorphismTuple Index B) (e : A.scheme ≅ B.scheme) (he : IsMonHom e.hom) :
    AbelianEndomorphism.ConjugateAbelianTuples e (k.conjugate e he) k := fun _ => rfl

def SmoothArithmetic.Abelian.SmoothArithmeticChart.enhancedFiberIso
    {X : Scheme} {f : X ⟶ Spec (CommRingCat.of ℚ)} {p : Spec (CommRingCat.of ℂ) ⟶ X}
    (C : SmoothArithmetic.Abelian.SmoothArithmeticChart f p) {g N r : ℕ} {δ : Fin g → ℕ}
    (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r X) :
    ModuliObjects.Abelian.EnhancedAbelianIso ((A.pullback C.map).pullback (Spec.map (CommRingCat.ofHom C.point.toRingHom)))
      (A.pullback p) :=
  EnhancedCoefficientComparisons.Abelian.iteratedEnhancedPullbackIso A C.map (Spec.map (CommRingCat.ofHom C.point.toRingHom)) p C.recovers

def SmoothArithmetic.Abelian.SmoothArithmeticChart.fiberTuple
    {X : Scheme} {f : X ⟶ Spec (CommRingCat.of ℚ)} {p : Spec (CommRingCat.of ℂ) ⟶ X}
    (C : SmoothArithmetic.Abelian.SmoothArithmeticChart f p) {g N r m : ℕ} {δ : Fin g → ℕ}
    (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r X)
    (k : AbelianEndomorphism.AbelianEndomorphismTuple (Fin m) (A.pullback p).polarized.abelian) :
    AbelianEndomorphism.AbelianEndomorphismTuple (Fin m)
      ((A.pullback C.map).pullback (Spec.map (CommRingCat.ofHom C.point.toRingHom))).polarized.abelian :=
  k.conjugate (C.enhancedFiberIso A).polarized.abelian (C.enhancedFiberIso A).polarized.abelianGroup

theorem SmoothArithmetic.Abelian.SmoothArithmeticChart.fiberTuple_comparison
    {X : Scheme} {f : X ⟶ Spec (CommRingCat.of ℚ)} {p : Spec (CommRingCat.of ℂ) ⟶ X}
    (C : SmoothArithmetic.Abelian.SmoothArithmeticChart f p) {g N r m : ℕ} {δ : Fin g → ℕ}
    (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r X)
    (k : AbelianEndomorphism.AbelianEndomorphismTuple (Fin m) (A.pullback p).polarized.abelian) :
    AbelianEndomorphism.ConjugateAbelianTuples (C.enhancedFiberIso A).polarized.abelian (C.fiberTuple A k) k :=
  k.conjugate_comparison _ _

def ModuliObjects.Abelian.EnhancedAbelianIso.extendPullback
    {g N r : ℕ} {δ : Fin g → ℕ} {X S T : Scheme}
    (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r X) (G : ModuliObjects.Abelian.EnhancedAbelianData g δ N r S)
    (j : S ⟶ X) (e : ModuliObjects.Abelian.EnhancedAbelianIso G (A.pullback j)) (f : T ⟶ S) :
    ModuliObjects.Abelian.EnhancedAbelianIso (G.pullback f) (A.pullback (f ≫ j)) :=
  (e.pullback f).trans (ModuliObjects.Abelian.EnhancedAbelianIso.pullbackComp A j f)

theorem AbelianEndomorphism.ConjugateAbelianTuples.trans_enhanced
    {g N r m : ℕ} {δ : Fin g → ℕ} {S : Scheme}
    {A B C : ModuliObjects.Abelian.EnhancedAbelianData g δ N r S}
    (e : ModuliObjects.Abelian.EnhancedAbelianIso A B) (d : ModuliObjects.Abelian.EnhancedAbelianIso B C)
    (a : AbelianEndomorphism.AbelianEndomorphismTuple (Fin m) A.polarized.abelian)
    (b : AbelianEndomorphism.AbelianEndomorphismTuple (Fin m) B.polarized.abelian)
    (c : AbelianEndomorphism.AbelianEndomorphismTuple (Fin m) C.polarized.abelian)
    (he : AbelianEndomorphism.ConjugateAbelianTuples e.polarized.abelian a b)
    (hd : AbelianEndomorphism.ConjugateAbelianTuples d.polarized.abelian b c) :
    AbelianEndomorphism.ConjugateAbelianTuples (e.trans d).polarized.abelian a c :=
  AbelianEndomorphism.ConjugateAbelianTuples.trans e.polarized.abelian d.polarized.abelian a b c he hd

end ArithmeticGeometry.Descent.CMVariety

namespace ArithmeticGeometry.Descent.CMVariety.EnhancedChart.Abelian

/-!
Construct a smooth integral arithmetic parameter carrying the original
enhanced family and any finite tuple of extra complex-fiber group maps.
The map to the original parameter, the global enhanced comparison, and
the full enhanced comparison on the specified fiber are actual data.
This is a parameter construction, not a moduli representability claim.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

structure SmoothEnhancedParameter {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of ℚ)) {g N r m : ℕ} {δ : Fin g → ℕ}
    (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r X) (p : Spec (CommRingCat.of ℂ) ⟶ X)
    (k : AbelianEndomorphism.AbelianEndomorphismTuple (Fin m) (A.pullback p).polarized.abelian) where
  space : Scheme
  map : space ⟶ X
  integral : IsIntegral space
  smooth : Smooth (map ≫ f)
  point : Spec (CommRingCat.of ℂ) ⟶ space
  point_eq : point ≫ map = p
  chart : SmoothArithmetic.Abelian.SmoothArithmeticChart f p
  chartMap : space ⟶ Spec (CommRingCat.of chart.ring)
  chartMap_smooth : Smooth chartMap
  map_eq : map = chartMap ≫ chart.map
  point_chart : point ≫ chartMap = Spec.map (CommRingCat.ofHom chart.point.toRingHom)
  family : ModuliObjects.Abelian.EnhancedAbelianData g δ N r space
  comparison : ModuliObjects.Abelian.EnhancedAbelianIso family (A.pullback map)
  extraTuple : AbelianEndomorphism.AbelianEndomorphismTuple (Fin m) family.polarized.abelian
  fiberComparison : ModuliObjects.Abelian.EnhancedAbelianIso (family.pullback point) (A.pullback p)
  extraRecovery : AbelianEndomorphism.ConjugateAbelianTuples fiberComparison.polarized.abelian
    (extraTuple.pullback point) k

attribute [instance] SmoothEnhancedParameter.integral SmoothEnhancedParameter.smooth
  SmoothEnhancedParameter.chartMap_smooth

theorem smooth_enhanced_parameter_exists
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℚ)) [LocallyOfFiniteType f]
    {g N r m : ℕ} {δ : Fin g → ℕ}
    (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r X) (p : Spec (CommRingCat.of ℂ) ⟶ X)
    (k : AbelianEndomorphism.AbelianEndomorphismTuple (Fin m) (A.pullback p).polarized.abelian) :
    Nonempty (SmoothEnhancedParameter f A p k) := by
  obtain ⟨C⟩ := SmoothArithmetic.Abelian.complex_point_has_smooth_arithmetic_chart f p
  let R := C.ring
  let : Algebra R ℂ := C.point.toRingHom.toAlgebra
  let : CharZero R := C.point.toRingHom.charZero
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℚ R
  have hR : Function.Injective (algebraMap R ℂ) := C.injective
  let pR := Spec.map (CommRingCat.ofHom (algebraMap R ℂ))
  let F := A.pullback C.map
  let kR : AbelianEndomorphism.AbelianEndomorphismTuple (Fin m) (F.pullback pR).polarized.abelian := C.fiberTuple A k
  obtain ⟨s, t, U, hU, hsm, q, hq, a, ha, _⟩ :=
    SmoothEnhancedTupleSpread.Abelian.enhanced_tuple_spreads_over_smooth_neighborhood R hR F kR
  let b₁ := FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R ℂ s.unop
  let b₂ := FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R ℂ s.unop) ℂ t.unop
  let v := U.ι ≫ AbelianEndomorphism.twoStageCoefficientBaseMap R ℂ s t
  let j := v ≫ C.map
  let G := (EnhancedCoefficientComparisons.Abelian.twoStageEnhancedFamily R ℂ F s t).pullback U.ι
  let : Smooth v := hsm
  let : Smooth (Spec.map (CommRingCat.ofHom (algebraMap ℚ R))) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (RingHom.smooth_algebraMap.mpr C.smooth)
  have hjsmooth : Smooth (j ≫ f) := by
    have hEq : j ≫ f = v ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ R)) := by
      change (v ≫ C.map) ≫ f = _
      rw [Category.assoc, C.structure_eq]
    rw [hEq]
    infer_instance
  have hqv : q ≫ v = pR := by
    calc
      q ≫ v = (q ≫ U.ι) ≫ AbelianEndomorphism.twoStageCoefficientBaseMap R ℂ s t := (Category.assoc _ _ _).symm
      _ = AbelianCoefficientComparison.coefficientInclusion (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R ℂ s.unop) ℂ t ≫
          AbelianEndomorphism.twoStageCoefficientBaseMap R ℂ s t := congrArg (fun u => u ≫ AbelianEndomorphism.twoStageCoefficientBaseMap R ℂ s t) hq
      _ = pR := AbelianEndomorphism.twoStageCoefficientInclusion_base R ℂ s t
  have hpoint : q ≫ j = p := by
    change q ≫ (v ≫ C.map) = p
    rw [← Category.assoc, hqv]
    exact C.recovers
  let e₁ := ModuliObjects.Abelian.EnhancedAbelianIso.pullbackComp A C.map b₁
  let e₂ := ModuliObjects.Abelian.EnhancedAbelianIso.extendPullback A (F.pullback b₁) (b₁ ≫ C.map) e₁ b₂
  let e₃ := ModuliObjects.Abelian.EnhancedAbelianIso.extendPullback A ((F.pullback b₁).pullback b₂)
    (b₂ ≫ b₁ ≫ C.map) e₂ U.ι
  have hj : U.ι ≫ (b₂ ≫ b₁ ≫ C.map) = j := by
    simp only [j, v, b₁, b₂, AbelianEndomorphism.twoStageCoefficientBaseMap, Category.assoc]
  let eGlobal : ModuliObjects.Abelian.EnhancedAbelianIso G (A.pullback j) :=
    e₃.trans (ModuliObjects.Abelian.EnhancedAbelianIso.pullbackCongr A (U.ι ≫ (b₂ ≫ b₁ ≫ C.map)) j hj)
  let eS : ModuliObjects.Abelian.EnhancedAbelianIso (G.pullback q) (F.pullback pR) :=
    SmoothEnhancedTupleSpread.Abelian.smoothCoefficientEnhancedComparison R F s t U q hq
  let eR : ModuliObjects.Abelian.EnhancedAbelianIso (F.pullback pR) (A.pullback p) := C.enhancedFiberIso A
  have hrec : AbelianEndomorphism.ConjugateAbelianTuples (eS.trans eR).polarized.abelian (a.pullback q) k :=
    AbelianEndomorphism.ConjugateAbelianTuples.trans_enhanced eS eR (a.pullback q) kR k ha (C.fiberTuple_comparison A k)
  exact ⟨{
    space := U
    map := j
    integral := hU
    smooth := hjsmooth
    point := q
    point_eq := hpoint
    chart := C
    chartMap := v
    chartMap_smooth := hsm
    map_eq := rfl
    point_chart := hqv
    family := G
    comparison := eGlobal
    extraTuple := a
    fiberComparison := eS.trans eR
    extraRecovery := hrec }⟩

end ArithmeticGeometry.Descent.CMVariety.EnhancedChart.Abelian

end

end OAI
