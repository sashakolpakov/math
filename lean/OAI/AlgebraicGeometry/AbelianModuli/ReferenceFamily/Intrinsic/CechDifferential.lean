import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.PairCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.Add

/-! # Cech Differential -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CechDifferential

noncomputable section

section

/-! Native values and holomorphic evaluations of the literal algebraic
Cech coefficients, including restriction and difference formulas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {I : Type} (U : I → V.carrier.Opens)

def nativeCechValue (n : ℕ) (W : V.carrier.Opens) (c : Γ(Cech.TermModules.cechTermModule V.carrier U n, W))
    (i : Fin (n + 1) → I) (x : V.analyticSpace)
    (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W ⊓ Cech.ExtensionCoordinates.cechIntersection U n i) : ℂ :=
  RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left (W ⊓ Cech.ExtensionCoordinates.cechIntersection U n i) hx (Cech.ExtensionCoordinates.cechCoefficient U n W c i)

def nativeCechCoefficient (n : ℕ) (W : V.carrier.Opens) (c : Γ(Cech.TermModules.cechTermModule V.carrier U n, W))
    (i : Fin (n + 1) → I) : DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel)
      (M := DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation (W ⊓ Cech.ExtensionCoordinates.cechIntersection U n i)) :=
  DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V (W ⊓ Cech.ExtensionCoordinates.cechIntersection U n i) (Cech.ExtensionCoordinates.cechCoefficient U n W c i)

theorem nativeCechCoefficient_value (n : ℕ) (W : V.carrier.Opens)
    (c : Γ(Cech.TermModules.cechTermModule V.carrier U n, W)) (i : Fin (n + 1) → I) (x : V.analyticSpace)
    (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W ⊓ Cech.ExtensionCoordinates.cechIntersection U n i) :
    nativeCechCoefficient V U n W c i ⟨x, hx⟩ = nativeCechValue V U n W c i x hx :=
  FrameEvaluation.sectionEvaluationOn_native V.presentation (W ⊓ Cech.ExtensionCoordinates.cechIntersection U n i) _ ⟨x, hx⟩

theorem nativeCechValue_congr_index (n : ℕ) (W : V.carrier.Opens)
    (c : Γ(Cech.TermModules.cechTermModule V.carrier U n, W)) {i j : Fin (n + 1) → I} (h : i = j)
    (x : V.analyticSpace) (hi : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W ⊓ Cech.ExtensionCoordinates.cechIntersection U n i)
    (hj : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W ⊓ Cech.ExtensionCoordinates.cechIntersection U n j) :
    nativeCechValue V U n W c i x hi = nativeCechValue V U n W c j x hj := by
  subst j
  rfl

theorem nativeCechValue_restrict (n : ℕ) {W Z : V.carrier.Opens} (h : Z ≤ W)
    (c : Γ(Cech.TermModules.cechTermModule V.carrier U n, W)) (i : Fin (n + 1) → I) (x : V.analyticSpace)
    (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ Z ⊓ Cech.ExtensionCoordinates.cechIntersection U n i) :
    nativeCechValue V U n Z ((Cech.TermModules.cechTermModule V.carrier U n).presheaf.map (homOfLE h).op c) i x hx =
      nativeCechValue V U n W c i x ⟨h hx.1, hx.2⟩ :=
  (congrArg (RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left (Z ⊓ Cech.ExtensionCoordinates.cechIntersection U n i) hx)
    (Cech.ExtensionCoordinates.cechCoefficient_restrict U n h c i)).trans
      (RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue_restrict x.left _ _ (inf_le_inf_right _ h) hx _)

theorem nativeCechValue_smul (n : ℕ) (W : V.carrier.Opens) (a : Γ(V.carrier, W))
    (c : Γ(Cech.TermModules.cechTermModule V.carrier U n, W)) (i : Fin (n + 1) → I) (x : V.analyticSpace)
    (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W ⊓ Cech.ExtensionCoordinates.cechIntersection U n i) :
    nativeCechValue V U n W (a • c) i x hx = RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left W hx.1 a *
      nativeCechValue V U n W c i x hx := by
  unfold nativeCechValue
  erw [Cech.ExtensionCoordinates.cechCoefficient_smul, map_mul, RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue_restrict]

theorem nativeCechValue_differential_zero (W : V.carrier.Opens)
    (a : Γ(Cech.TermModules.cechTermModule V.carrier U 0, W)) (i : Fin 2 → I) (x : V.analyticSpace)
    (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W ⊓ Cech.ExtensionCoordinates.cechIntersection U 1 i) :
    nativeCechValue V U 1 W ((Cech.ModuleDifferential.cechModuleDifferential V.carrier U 0).app W a) i x hx =
      nativeCechValue V U 0 W a (Cech.ExtensionCoordinates.cechFaceIndex 0 0 i) x ⟨hx.1, Cech.ExtensionCoordinates.cechIntersection_le_face U 0 0 i hx.2⟩ -
      nativeCechValue V U 0 W a (Cech.ExtensionCoordinates.cechFaceIndex 0 1 i) x ⟨hx.1, Cech.ExtensionCoordinates.cechIntersection_le_face U 0 1 i hx.2⟩ := by
  unfold nativeCechValue
  erw [Cech.PairCoordinates.cechCoefficient_differential_zero, map_sub, RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue_restrict,
    RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue_restrict]
  rfl

end

section

/-! Addition and the original augmentation in native Cech values. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.TopCat.Sheaf

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {I : Type} (U : I → V.carrier.Opens)

theorem nativeCechValue_add (n : ℕ) (W : V.carrier.Opens)
    (a b : Γ(Cech.TermModules.cechTermModule V.carrier U n, W)) (i : Fin (n + 1) → I) (x : V.analyticSpace)
    (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W ⊓ Cech.ExtensionCoordinates.cechIntersection U n i) :
    nativeCechValue V U n W (a + b) i x hx =
      nativeCechValue V U n W a i x hx + nativeCechValue V U n W b i x hx := by
  unfold nativeCechValue
  erw [Cech.ExtensionCoordinates.cechCoefficient_add, map_add]

theorem nativeCechValue_augmentation (W : V.carrier.Opens) (a : Γ(V.carrier, W))
    (i : Fin 1 → I) (x : V.analyticSpace)
    (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 i) :
    nativeCechValue V U 0 W ((Cech.ModuleAugmentation.cechModuleAugmentation V.carrier U).app W a) i x hx =
      RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left W hx.1 a := by
  have he := congrArg (fun f => f.hom.app (.op W) a) (Cech.ModuleAugmentation.cechModuleAugmentation_underlying V.carrier U)
  have hc : Cech.ExtensionCoordinates.cechCoefficient U 0 W ((Cech.ModuleAugmentation.cechModuleAugmentation V.carrier U).app W a) i =
      V.carrier.presheaf.map (homOfLE (show W ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 i ≤ W from inf_le_left)).op a :=
    (congrArg (fun b => Cech.ExtensionCoordinates.cechCoefficient U 0 W b i) he).trans
      (SheafCohomology.Cech.Augmentation.TopCat.Sheaf.cechAugmentation_apply (Cech.TermModules.structureAbelianSheaf V.carrier) U W a i)
  exact (congrArg (RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left (W ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 i) hx) hc).trans
    (RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue_restrict x.left W _ inf_le_left hx a)

end

section

/-! Evaluation commutes with the original alternating Cech differential
in every degree, at literal complex points of the intersections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {I : Type} (U : I → V.carrier.Opens)

theorem nativeCechValue_zero (n : ℕ) (W : V.carrier.Opens) (i : Fin (n + 1) → I)
    (x : V.analyticSpace) (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W ⊓ Cech.ExtensionCoordinates.cechIntersection U n i) :
    nativeCechValue V U n W 0 i x hx = 0 := by
  have hc : Cech.ExtensionCoordinates.cechCoefficient U n W 0 i = 0 :=
    congrArg (fun c => c i) ((SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv
      (Cech.TermModules.structureAbelianSheaf V.carrier) U n W).map_zero)
  unfold nativeCechValue
  erw [hc, map_zero]

theorem nativeCechValue_differential (n : ℕ) (W : V.carrier.Opens)
    (c : Γ(Cech.TermModules.cechTermModule V.carrier U n, W)) (i : Fin (n + 2) → I)
    (x : V.analyticSpace) (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W ⊓ Cech.ExtensionCoordinates.cechIntersection U (n + 1) i) :
    nativeCechValue V U (n + 1) W ((Cech.ModuleDifferential.cechModuleDifferential V.carrier U n).app W c) i x hx =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        nativeCechValue V U n W c (Cech.ExtensionCoordinates.cechFaceIndex n k i) x
          ⟨hx.1, Cech.ExtensionCoordinates.cechIntersection_le_face U n k i hx.2⟩ := by
  unfold nativeCechValue
  erw [Cech.ExtensionCoordinates.cechCoefficient_differential, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  erw [map_zsmul, RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue_restrict]
  rfl

end

section

/-! Literal holomorphic Cech cochains obtained by evaluating the original
algebraic Cech module sections on the native analytic cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {I : Type} (U : I → V.carrier.Opens)

def nativeCechCover (i : I) : Opens V.analyticSpace :=
  DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation (U i)

theorem nativeCechIntersection_mem (n : ℕ) (i : Fin (n + 1) → I) (x : V.analyticSpace) :
    x ∈ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (nativeCechCover V U) i ↔
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ Cech.ExtensionCoordinates.cechIntersection U n i := by
  rw [AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection, Cech.ExtensionCoordinates.cechIntersection, SheafCohomology.Cech.Cochains.TopologicalSpace.Opens.piObj_eq_iInf]
  exact (AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection (X := TopCat.of V.carrier) U i
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x)).symm

theorem nativeCechCover_covers (hU : iSup U = ⊤) : iSup (nativeCechCover V U) = ⊤ := by
  apply top_unique
  intro x _
  have hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

def nativeCechCochain (n : ℕ) (c : Γ(Cech.TermModules.cechTermModule V.carrier U n, ⊤)) :
    DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace).obj
      (nativeCechCover V U) n :=
  fun i => DivisorClass.Chern.HolomorphicSection.Data.holomorphicOpenRestriction
    (show AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (nativeCechCover V U) i ≤
      DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation (⊤ ⊓ Cech.ExtensionCoordinates.cechIntersection U n i) from
        fun x hx => ⟨trivial, (nativeCechIntersection_mem V U n i x).mp hx⟩)
    (nativeCechCoefficient V U n ⊤ c i)

def nativeCechFunction (n : ℕ) (c : Γ(Cech.TermModules.cechTermModule V.carrier U n, ⊤)) (i : Fin (n + 1) → I) :
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel)
      (M := AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (nativeCechCover V U) i) :=
  nativeCechCochain V U n c i

theorem nativeCechCochain_value (n : ℕ) (c : Γ(Cech.TermModules.cechTermModule V.carrier U n, ⊤))
    (i : Fin (n + 1) → I) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (nativeCechCover V U) i) :
    nativeCechFunction V U n c i x = nativeCechValue V U n ⊤ c i x.val
      ⟨trivial, (nativeCechIntersection_mem V U n i x.val).mp x.property⟩ :=
  nativeCechCoefficient_value V U n ⊤ c i x.val _

end

/-! The literal native evaluation cochains commute with the original
abelian Cech differential; algebraic cycles give native holomorphic cycles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {I : Type} (U : I → V.carrier.Opens)

theorem nativeCechCochain_zero (n : ℕ) : nativeCechCochain V U n 0 = 0 := by
  funext i
  change nativeCechFunction V U n 0 i = 0
  apply DFunLike.ext
  intro x
  exact (nativeCechCochain_value V U n 0 i x).trans (nativeCechValue_zero V U n ⊤ i x.val _)

theorem nativeCechCochain_differential (n : ℕ) (c : Γ(Cech.TermModules.cechTermModule V.carrier U n, ⊤)) :
    nativeCechCochain V U (n + 1) ((Cech.ModuleDifferential.cechModuleDifferential V.carrier U n).app ⊤ c) =
      DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace).obj
        (nativeCechCover V U) n (nativeCechCochain V U n c) := by
  funext i
  change nativeCechFunction V U (n + 1) ((Cech.ModuleDifferential.cechModuleDifferential V.carrier U n).app ⊤ c) i =
    (show DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel)
      (M := AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (nativeCechCover V U) i) from
        DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace).obj
          (nativeCechCover V U) n (nativeCechCochain V U n c) i)
  apply DFunLike.ext
  intro x
  rw [nativeCechCochain_value]
  erw [nativeCechValue_differential]
  change _ = ContMDiffMap.evalRingHom x
    (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
      (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace).obj.map
        (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp
          (nativeCechCover V U) i k.succAbove)).op
        (nativeCechCochain V U n c (i ∘ k.succAbove)))
  erw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  erw [map_zsmul]
  change _ = (-1 : ℤ) ^ (k : ℕ) • nativeCechFunction V U n c (i ∘ k.succAbove)
    ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp
      (nativeCechCover V U) i k.succAbove x.property⟩
  erw [nativeCechCochain_value]
  rfl

theorem nativeCechCochain_closed (n : ℕ) (c : Γ(Cech.TermModules.cechTermModule V.carrier U n, ⊤))
    (hc : (Cech.ModuleDifferential.cechModuleDifferential V.carrier U n).app ⊤ c = 0) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace).obj
      (nativeCechCover V U) n (nativeCechCochain V U n c) = 0 := by
  rw [← nativeCechCochain_differential, hc, nativeCechCochain_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CechDifferential
