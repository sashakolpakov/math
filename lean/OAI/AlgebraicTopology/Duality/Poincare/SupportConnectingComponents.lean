import OAI.AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris
import OAI.AlgebraicTopology.Duality.Poincare.AdditiveConnectingLifts

/-! # Support Connecting Components -/

namespace OAI.AlgebraicTopology.Duality.Poincare.SupportConnectingComponents

noncomputable section

section

/-!
# Genuine relative-cochain representatives for the support connecting map

The first endpoint of the binary dual sequence is computed by genuine
relative rational cochains through the proved small-chain quasi-isomorphism.
Its evaluation is the actual evaluation of the original relative cochain.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The genuine relative rational cochain complex maps to the first
endpoint by duality and precomposition with the actual small-chain comparison. -/
def binaryRelativeFirstEndpointMap (X : TopCat.{0}) (A B : Set X) :
    RelativeCochainDual.rationalCochainsForget.obj (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)) ⟶
      (SupportCohomologyMayerVietoris.binaryRelativeDualSequence X A B).X₁ :=
  (RelativeCochainDual.relativeCochainIntegralDualIso X (A ∪ B)).hom ≫
    RelativeCochainDual.rationalChainDualMap (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B)

/-- The actual endpoint comparison is a quasi-isomorphism for open sets. -/
theorem binaryRelativeFirstEndpointMap_quasiIso (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) : QuasiIso (binaryRelativeFirstEndpointMap X A B) := by
  have : QuasiIso (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B) :=
    AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative_quasiIso X A B hA hB
  have : QuasiIso (RelativeCochainDual.rationalChainDualMap (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B)) :=
    CompactSupportExcision.rationalChainDualMap_quasiIso _
  change QuasiIso ((RelativeCochainDual.relativeCochainIntegralDualIso X (A ∪ B)).hom ≫
    RelativeCochainDual.rationalChainDualMap (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B))
  infer_instance

/-- Pulling the endpoint functional back to an ordinary integral chain is
exactly evaluation of the original relative rational cochain. -/
@[reassoc]
theorem binaryRelativeFirstEndpointMap_projection (X : TopCat.{0}) (A B : Set X) :
    binaryRelativeFirstEndpointMap X A B ≫
        RelativeCochainDual.rationalChainDualMap (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B) =
      RelativeCochainDual.rationalCochainsForget.map (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (A ∪ B)) ≫
        (RelativeCochainDual.rationalSingularCochainDualIso X).hom := by
  rw [binaryRelativeFirstEndpointMap, Category.assoc, ← RelativeCochainDual.rationalChainDualMap_comp,
    AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative_projection, RelativeCochainDual.relativeCochainIntegralDualIso_projection]

/-- The explicit finite-chain evaluation formula for the genuine first endpoint. -/
theorem binaryRelativeFirstEndpointMap_eval_projection (X : TopCat.{0}) (A B : Set X)
    (n : ℕ) (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)).X n)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    (show (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).X n ⟶ RelativeCochainDual.rationalIntegralCoefficient from
        (binaryRelativeFirstEndpointMap X A B).f n c)
        ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f n z) =
      RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj X) n
        ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (A ∪ B)).f n c) z := by
  have he := ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (binaryRelativeFirstEndpointMap_projection X A B) n) c
  exact congrArg (fun t : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n ⟶ RelativeCochainDual.rationalIntegralCoefficient => t z) he

/-- The endpoint homology comparison recovers exactly the native rational
relative-cohomology class, with only its scalars forgotten. -/
@[reassoc]
theorem binaryRelativeFirstEndpointMap_homology (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    HomologicalComplex.homologyMap (binaryRelativeFirstEndpointMap X A B) n ≫
        (SupportCohomologyMayerVietoris.binaryRelativeDualFirstHomologyIso X A B hA hB n).hom =
      (SupportCohomologyMayerVietoris.rationalCochainHomologyForgetIso
        (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)) n).hom := by
  apply (cancel_mono (SupportCohomologyMayerVietoris.binaryRelativeDualFirstHomologyIso X A B hA hB n).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    SupportCohomologyMayerVietoris.binaryRelativeDualFirstHomologyIso_inv]
  simp only [binaryRelativeFirstEndpointMap, HomologicalComplex.homologyMap_comp,
    SupportCohomologyMayerVietoris.relativeRationalCohomologyDualIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  rfl

/-- The native relative connecting map is the actual additive connecting
map under the proved endpoint isomorphisms. -/
@[reassoc]
theorem binaryRelativeBoundary_endpoint_comparison (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    (SupportCohomologyMayerVietoris.binaryRelativeDualThirdHomologyIso X A B n).hom ≫
        (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map
          (SupportCohomologyMayerVietoris.relativeRationalMayerVietorisBoundary X A B hA hB n) =
      (SupportCohomologyMayerVietoris.binaryRelativeDualSequence_shortExact X A B).δ n (n + 1) rfl ≫
        (SupportCohomologyMayerVietoris.binaryRelativeDualFirstHomologyIso X A B hA hB (n + 1)).hom := by
  rw [SupportCohomologyMayerVietoris.relativeRationalMayerVietorisBoundary_forget, Iso.hom_inv_id_assoc]

/-- A connecting representative can be chosen in the genuine relative
rational cochain complex. The middle cochain is adjusted by the image of
an actual primitive so its differential equals this prescribed endpoint
representative. Only the proved endpoint quasi-isomorphism is used. -/
theorem supportConnecting_representatives (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ)
    (x₃ : (SupportCohomologyMayerVietoris.binaryRelativeDualSequence X A B).X₃.cycles n) :
    ∃ (c : (RelativeCochainDual.rationalCochainsForget.obj
        (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B))).cycles (n + 1))
      (b₂ : (SupportCohomologyMayerVietoris.binaryRelativeDualSequence X A B).X₂.X n),
      (SupportCohomologyMayerVietoris.binaryRelativeDualSequence X A B).g.f n b₂ =
        (SupportCohomologyMayerVietoris.binaryRelativeDualSequence X A B).X₃.iCycles n x₃ ∧
      (SupportCohomologyMayerVietoris.binaryRelativeDualSequence X A B).X₂.d n (n + 1) b₂ =
        (SupportCohomologyMayerVietoris.binaryRelativeDualSequence X A B).f.f (n + 1)
          ((binaryRelativeFirstEndpointMap X A B).f (n + 1)
            ((RelativeCochainDual.rationalCochainsForget.obj
              (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B))).iCycles (n + 1) c)) ∧
      (SupportCohomologyMayerVietoris.rationalCochainHomologyForgetIso
          (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)) (n + 1)).hom
          ((RelativeCochainDual.rationalCochainsForget.obj
            (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B))).homologyπ (n + 1) c) =
        SupportCohomologyMayerVietoris.relativeRationalMayerVietorisBoundary X A B hA hB n
          ((SupportCohomologyMayerVietoris.binaryRelativeDualThirdHomologyIso X A B n).hom
            ((SupportCohomologyMayerVietoris.binaryRelativeDualSequence X A B).X₃.homologyπ n x₃)) := by
  let S := SupportCohomologyMayerVietoris.binaryRelativeDualSequence X A B
  let T := RelativeCochainDual.rationalCochainsForget.obj
    (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B))
  let F : T ⟶ S.X₁ := binaryRelativeFirstEndpointMap X A B
  have : QuasiIso F := binaryRelativeFirstEndpointMap_quasiIso X A B hA hB
  obtain ⟨b₂, c, hb₂, hc, hclass⟩ := AdditiveConnectingLifts.additiveConnecting_representatives_through_quasiIso
    S (SupportCohomologyMayerVietoris.binaryRelativeDualSequence_shortExact X A B) F n x₃
  refine ⟨c, b₂, hb₂, hc.symm, ?_⟩
  have hF := ConcreteCategory.congr_hom
    (binaryRelativeFirstEndpointMap_homology X A B hA hB (n + 1))
    (T.homologyπ (n + 1) c)
  have hδ := ConcreteCategory.congr_hom
    (binaryRelativeBoundary_endpoint_comparison X A B hA hB n)
    (S.X₃.homologyπ n x₃)
  exact hF.symm.trans ((congrArg
    (SupportCohomologyMayerVietoris.binaryRelativeDualFirstHomologyIso X A B hA hB (n + 1)).hom hclass).trans hδ.symm)

end

/-!
# Ordinary relative cochain components of support-connecting lifts

The dual-sequence representatives are converted into actual relative
rational cochains using the proved duality isomorphisms. All scalar
forgetting comparisons preserve the underlying cochain and its class.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Scalar forgetting commutes with the native cycle-to-cohomology projection. -/
@[reassoc]
theorem rationalCochainHomologyForgetIso_homologyπ
    (C : CochainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ) :
    (RelativeCochainDual.rationalCochainsForget.obj C).homologyπ n ≫
        (SupportCohomologyMayerVietoris.rationalCochainHomologyForgetIso C n).hom =
      ((C.sc n).mapCyclesIso (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0})).hom ≫
        (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map (C.homologyπ n) := by
  let S := C.sc n
  let G := forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}
  change (S.map G).homologyπ ≫ (S.mapHomologyIso G).hom =
    (S.mapCyclesIso G).hom ≫ G.map S.homologyπ
  rw [S.leftHomologyData.mapHomologyIso_eq G, S.leftHomologyData.mapCyclesIso_eq G]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  simp only [Category.assoc, ShortComplex.LeftHomologyData.map_π]
  rw [← G.map_comp, S.leftHomologyData.π_comp_homologyIso_inv, G.map_comp]

/-- A genuine rational cocycle gives the same native cycle after forgetting scalars. -/
def rationalCocycleToForgottenCycle (C : CochainComplex (ModuleCat.{0} ℚ) ℕ)
    (n : ℕ) (c : Cohomology.Singular.Representatives.cochainCocycles C n) : (RelativeCochainDual.rationalCochainsForget.obj C).cycles n :=
  ((C.sc n).mapCyclesIso (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0})).inv
    ((C.sc n).moduleCatCyclesIso.inv c)

/-- The scalar-forgetting cycle comparison preserves the actual cochain. -/
@[simp]
theorem rationalCocycleToForgottenCycle_val (C : CochainComplex (ModuleCat.{0} ℚ) ℕ)
    (n : ℕ) (c : Cohomology.Singular.Representatives.cochainCocycles C n) :
    (RelativeCochainDual.rationalCochainsForget.obj C).iCycles n (rationalCocycleToForgottenCycle C n c) = c.val := by
  let e := (C.sc n).mapCyclesIso (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0})
  have h := ConcreteCategory.congr_hom
    ((C.sc n).mapCyclesIso_hom_iCycles (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}))
    (rationalCocycleToForgottenCycle C n c)
  have he : e.hom (e.inv ((C.sc n).moduleCatCyclesIso.inv c)) =
      (C.sc n).moduleCatCyclesIso.inv c :=
    ConcreteCategory.congr_hom e.inv_hom_id ((C.sc n).moduleCatCyclesIso.inv c)
  change C.iCycles n (e.hom (e.inv ((C.sc n).moduleCatCyclesIso.inv c))) =
    (RelativeCochainDual.rationalCochainsForget.obj C).iCycles n (rationalCocycleToForgottenCycle C n c) at h
  rw [he] at h
  exact h.symm.trans (ConcreteCategory.congr_hom ((C.sc n).moduleCatCyclesIso_inv_iCycles) c)

/-- Every native cycle of the scalar-forgotten complex is the same genuine rational cocycle. -/
def forgottenCycleToRationalCocycle (C : CochainComplex (ModuleCat.{0} ℚ) ℕ)
    (n : ℕ) (x : (RelativeCochainDual.rationalCochainsForget.obj C).cycles n) : Cohomology.Singular.Representatives.cochainCocycles C n :=
  ⟨(RelativeCochainDual.rationalCochainsForget.obj C).iCycles n x, by
    apply (Cohomology.Singular.Representatives.mem_cochainCocycles_iff C n _).mpr
    exact ConcreteCategory.congr_hom ((RelativeCochainDual.rationalCochainsForget.obj C).iCycles_d n (n + 1)) x⟩

@[simp]
theorem forgottenCycleToRationalCocycle_val (C : CochainComplex (ModuleCat.{0} ℚ) ℕ)
    (n : ℕ) (x : (RelativeCochainDual.rationalCochainsForget.obj C).cycles n) :
    (forgottenCycleToRationalCocycle C n x).val = (RelativeCochainDual.rationalCochainsForget.obj C).iCycles n x := rfl

/-- The cycle comparison preserves the native rational cohomology class. -/
theorem rationalCocycleToForgottenCycle_class (C : CochainComplex (ModuleCat.{0} ℚ) ℕ)
    (n : ℕ) (c : Cohomology.Singular.Representatives.cochainCocycles C n) :
    (SupportCohomologyMayerVietoris.rationalCochainHomologyForgetIso C n).hom
        ((RelativeCochainDual.rationalCochainsForget.obj C).homologyπ n (rationalCocycleToForgottenCycle C n c)) =
      Cohomology.Singular.Representatives.cochainClass C n c := by
  rw [Cohomology.Singular.Representatives.cochainClass_eq_homologyπ]
  have h := ConcreteCategory.congr_hom (rationalCochainHomologyForgetIso_homologyπ C n)
    (rationalCocycleToForgottenCycle C n c)
  let e := (C.sc n).mapCyclesIso (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0})
  have he : e.hom (e.inv ((C.sc n).moduleCatCyclesIso.inv c)) =
      (C.sc n).moduleCatCyclesIso.inv c :=
    ConcreteCategory.congr_hom e.inv_hom_id ((C.sc n).moduleCatCyclesIso.inv c)
  change _ = C.homologyπ n (e.hom (e.inv ((C.sc n).moduleCatCyclesIso.inv c))) at h
  rwa [he] at h

theorem forgottenCycleToRationalCocycle_class (C : CochainComplex (ModuleCat.{0} ℚ) ℕ)
    (n : ℕ) (x : (RelativeCochainDual.rationalCochainsForget.obj C).cycles n) :
    Cohomology.Singular.Representatives.cochainClass C n (forgottenCycleToRationalCocycle C n x) =
      (SupportCohomologyMayerVietoris.rationalCochainHomologyForgetIso C n).hom ((RelativeCochainDual.rationalCochainsForget.obj C).homologyπ n x) := by
  have hx : rationalCocycleToForgottenCycle C n (forgottenCycleToRationalCocycle C n x) = x := by
    apply (AddCommGrpCat.mono_iff_injective ((RelativeCochainDual.rationalCochainsForget.obj C).iCycles n)).mp inferInstance
    rw [rationalCocycleToForgottenCycle_val, forgottenCycleToRationalCocycle_val]
  rw [← rationalCocycleToForgottenCycle_class, hx]

/-- A relative rational cocycle gives its actual functional-valued native cycle. -/
def relativeDualCocycle (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (a : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) n) :
    (RelativeCochainDual.rationalChainDual (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A)).cycles n :=
  HomologicalComplex.cyclesMap (RelativeCochainDual.relativeCochainIntegralDualIso X A).hom n
    (rationalCocycleToForgottenCycle _ n a)

@[simp]
theorem relativeDualCocycle_val (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (a : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) n) :
    (RelativeCochainDual.rationalChainDual (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A)).iCycles n
        (relativeDualCocycle X A n a) =
      (RelativeCochainDual.relativeCochainIntegralDualIso X A).hom.f n a.val := by
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (RelativeCochainDual.relativeCochainIntegralDualIso X A).hom n)
    (rationalCocycleToForgottenCycle _ n a)
  change _ = (RelativeCochainDual.relativeCochainIntegralDualIso X A).hom.f n
    ((RelativeCochainDual.rationalCochainsForget.obj _).iCycles n (rationalCocycleToForgottenCycle _ n a)) at h
  rwa [rationalCocycleToForgottenCycle_val] at h

/-- Conversion to the dual-complex cycle preserves the genuine relative class. -/
theorem relativeDualCocycle_class (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (a : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) n) :
    (SupportCohomologyMayerVietoris.relativeRationalCohomologyDualIso X A n).inv
        ((RelativeCochainDual.rationalChainDual (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A)).homologyπ n
          (relativeDualCocycle X A n a)) =
      Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) n a := by
  let C := Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A
  have hc : HomologicalComplex.homologyMap (RelativeCochainDual.relativeCochainIntegralDualIso X A).hom n ≫
        (SupportCohomologyMayerVietoris.relativeRationalCohomologyDualIso X A n).inv =
      (SupportCohomologyMayerVietoris.rationalCochainHomologyForgetIso C n).hom := by
    apply (cancel_mono (SupportCohomologyMayerVietoris.relativeRationalCohomologyDualIso X A n).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    dsimp only [C]
    simp only [SupportCohomologyMayerVietoris.relativeRationalCohomologyDualIso, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Iso.hom_inv_id_assoc]
    rfl
  have hπ := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (RelativeCochainDual.relativeCochainIntegralDualIso X A).hom n)
    (rationalCocycleToForgottenCycle C n a)
  have hclass := ConcreteCategory.congr_hom hc
    ((RelativeCochainDual.rationalCochainsForget.obj C).homologyπ n (rationalCocycleToForgottenCycle C n a))
  exact (congrArg (SupportCohomologyMayerVietoris.relativeRationalCohomologyDualIso X A n).inv hπ.symm).trans
    (hclass.trans (rationalCocycleToForgottenCycle_class C n a))

/-- Restriction from a larger vanishing set to a smaller one. -/
abbrev relativeRationalSubsetCochainMap (X : TopCat.{0}) {A B : Set X} (h : A ⊆ B) :
    Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B ⟶
      Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A :=
  Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) (𝟙 X) (fun _ hx => h hx)

@[reassoc]
theorem relativeRationalSubsetCochainMap_inclusion (X : TopCat.{0})
    {A B : Set X} (h : A ⊆ B) :
    relativeRationalSubsetCochainMap X h ≫
        Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A =
      Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B := by
  simpa only [Cohomology.Singular.Functor.singularPullback_id, Category.comp_id] using
    Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality (ModuleCat.of ℚ ℚ) (𝟙 X) (fun _ hx => h hx)

@[reassoc]
theorem relativeRationalSubsetCochainMap_dual (X : TopCat.{0})
    {A B : Set X} (h : A ⊆ B) :
    RelativeCochainDual.rationalCochainsForget.map (relativeRationalSubsetCochainMap X h) ≫
        (RelativeCochainDual.relativeCochainIntegralDualIso X A).hom =
      (RelativeCochainDual.relativeCochainIntegralDualIso X B).hom ≫
        RelativeCochainDual.rationalChainDualMap (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X h) :=
  RelativeCochainDual.relativeCochainIntegralDualIso_naturality (𝟙 X) (fun _ hx => h hx)

@[reassoc]
theorem relativeRationalSubsetCochainMap_dual_conjugate (X : TopCat.{0})
    {A B : Set X} (h : A ⊆ B) :
    (RelativeCochainDual.relativeCochainIntegralDualIso X B).hom ≫
        RelativeCochainDual.rationalChainDualMap (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X h) ≫
        (RelativeCochainDual.relativeCochainIntegralDualIso X A).inv =
      RelativeCochainDual.rationalCochainsForget.map (relativeRationalSubsetCochainMap X h) := by
  rw [← Category.assoc, ← relativeRationalSubsetCochainMap_dual,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The first actual relative cochain carried by a dual-middle cochain. -/
def supportConnectingLeftComponent (X : TopCat.{0}) (A B : Set X) :
    (SupportCohomologyMayerVietoris.binaryRelativeDualSequence X A B).X₂ ⟶
      RelativeCochainDual.rationalCochainsForget.obj (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) :=
  RelativeCochainDual.rationalChainDualMap
      (biprod.inl : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A ⟶
        AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A ⊞ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B) ≫
    (RelativeCochainDual.relativeCochainIntegralDualIso X A).inv

/-- The second actual relative cochain carried by a dual-middle cochain. -/
def supportConnectingRightComponent (X : TopCat.{0}) (A B : Set X) :
    (SupportCohomologyMayerVietoris.binaryRelativeDualSequence X A B).X₂ ⟶
      RelativeCochainDual.rationalCochainsForget.obj (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B) :=
  RelativeCochainDual.rationalChainDualMap
      (biprod.inr : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B ⟶
        AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A ⊞ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B) ≫
    (RelativeCochainDual.relativeCochainIntegralDualIso X B).inv

@[reassoc]
theorem supportConnectingLeftComponent_first (X : TopCat.{0}) (A B : Set X) :
    binaryRelativeFirstEndpointMap X A B ≫ (SupportCohomologyMayerVietoris.binaryRelativeDualSequence X A B).f ≫
        supportConnectingLeftComponent X A B =
      RelativeCochainDual.rationalCochainsForget.map (relativeRationalSubsetCochainMap X
        (Set.subset_union_left : A ⊆ A ∪ B)) := by
  have hc : (biprod.inl : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A ⟶
        AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A ⊞ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B) ≫
        (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence X A B).g ≫ AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B =
      AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X (Set.subset_union_left : A ⊆ A ∪ B) := by
    simp [AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence]
  have hd := congrArg (fun f => RelativeCochainDual.rationalChainDualMap f) hc
  simp only [RelativeCochainDual.rationalChainDualMap_comp, Category.assoc] at hd
  have he := congrArg (fun f => (RelativeCochainDual.relativeCochainIntegralDualIso X (A ∪ B)).hom ≫ f ≫
    (RelativeCochainDual.relativeCochainIntegralDualIso X A).inv) hd
  simpa only [binaryRelativeFirstEndpointMap, SupportCohomologyMayerVietoris.binaryRelativeDualSequence_f,
    supportConnectingLeftComponent, Category.assoc] using
    he.trans (relativeRationalSubsetCochainMap_dual_conjugate X Set.subset_union_left)

@[reassoc]
theorem supportConnectingRightComponent_first (X : TopCat.{0}) (A B : Set X) :
    binaryRelativeFirstEndpointMap X A B ≫ (SupportCohomologyMayerVietoris.binaryRelativeDualSequence X A B).f ≫
        supportConnectingRightComponent X A B =
      RelativeCochainDual.rationalCochainsForget.map (relativeRationalSubsetCochainMap X
        (Set.subset_union_right : B ⊆ A ∪ B)) := by
  have hc : (biprod.inr : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B ⟶
        AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A ⊞ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B) ≫
        (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence X A B).g ≫ AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B =
      AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X (Set.subset_union_right : B ⊆ A ∪ B) := by
    simp [AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence]
  have hd := congrArg (fun f => RelativeCochainDual.rationalChainDualMap f) hc
  simp only [RelativeCochainDual.rationalChainDualMap_comp, Category.assoc] at hd
  have he := congrArg (fun f => (RelativeCochainDual.relativeCochainIntegralDualIso X (A ∪ B)).hom ≫ f ≫
    (RelativeCochainDual.relativeCochainIntegralDualIso X B).inv) hd
  simpa only [binaryRelativeFirstEndpointMap, SupportCohomologyMayerVietoris.binaryRelativeDualSequence_f,
    supportConnectingRightComponent, Category.assoc] using
    he.trans (relativeRationalSubsetCochainMap_dual_conjugate X Set.subset_union_right)

@[simp]
theorem rationalChainDualMap_sub
    {C D : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f g : C ⟶ D) :
    RelativeCochainDual.rationalChainDualMap (f - g) = RelativeCochainDual.rationalChainDualMap f - RelativeCochainDual.rationalChainDualMap g := by
  change RelativeCochainDual.rationalChainDualFunctor.map (f - g).op =
    RelativeCochainDual.rationalChainDualFunctor.map f.op - RelativeCochainDual.rationalChainDualFunctor.map g.op
  rw [op_sub, Functor.map_sub]

/-- The signed middle map is the difference of its two relative components. -/
@[reassoc]
theorem supportConnectingComponents_difference_relative (X : TopCat.{0}) (A B : Set X) :
    supportConnectingLeftComponent X A B ≫
        RelativeCochainDual.rationalCochainsForget.map (relativeRationalSubsetCochainMap X
          (Set.inter_subset_left : A ∩ B ⊆ A)) -
      supportConnectingRightComponent X A B ≫
        RelativeCochainDual.rationalCochainsForget.map (relativeRationalSubsetCochainMap X
          (Set.inter_subset_right : A ∩ B ⊆ B)) =
      (SupportCohomologyMayerVietoris.binaryRelativeDualSequence X A B).g ≫
        (RelativeCochainDual.relativeCochainIntegralDualIso X (A ∩ B)).inv := by
  apply (cancel_mono (RelativeCochainDual.relativeCochainIntegralDualIso X (A ∩ B)).hom).mp
  simp only [Preadditive.sub_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    relativeRationalSubsetCochainMap_dual, supportConnectingLeftComponent,
    supportConnectingRightComponent, Iso.inv_hom_id_assoc, SupportCohomologyMayerVietoris.binaryRelativeDualSequence_g]
  have hf : (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence X A B).f =
      AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X (Set.inter_subset_left : A ∩ B ⊆ A) ≫ biprod.inl -
      AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X (Set.inter_subset_right : A ∩ B ⊆ B) ≫ biprod.inr := by
    simp only [AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence, biprod.lift_eq, Preadditive.neg_comp, sub_eq_add_neg]
  rw [hf, rationalChainDualMap_sub, RelativeCochainDual.rationalChainDualMap_comp, RelativeCochainDual.rationalChainDualMap_comp]

/-- The ordinary ambient cochain is exactly the signed difference of both components. -/
@[reassoc]
theorem supportConnectingComponents_difference (X : TopCat.{0}) (A B : Set X) :
    supportConnectingLeftComponent X A B ≫
        RelativeCochainDual.rationalCochainsForget.map (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A) -
      supportConnectingRightComponent X A B ≫
        RelativeCochainDual.rationalCochainsForget.map (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B) =
      (SupportCohomologyMayerVietoris.binaryRelativeDualSequence X A B).g ≫
        (RelativeCochainDual.relativeCochainIntegralDualIso X (A ∩ B)).inv ≫
        RelativeCochainDual.rationalCochainsForget.map (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (A ∩ B)) := by
  have h := congrArg (fun f => f ≫ RelativeCochainDual.rationalCochainsForget.map
    (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (A ∩ B)))
    (supportConnectingComponents_difference_relative X A B)
  simpa only [Preadditive.sub_comp, Category.assoc, ← Functor.map_comp,
    relativeRationalSubsetCochainMap_inclusion] using h

/-- A cochain map carries a prescribed differential to its composite lift. -/
private theorem supportConnecting_component_differential_of_lift
    {C D E : CochainComplex AddCommGrpCat.{0} ℕ}
    (F : C ⟶ D) (G : D ⟶ E) (n : ℕ) (b : D.X n) (z : C.X (n + 1))
    (h : D.d n (n + 1) b = F.f (n + 1) z) :
    E.d n (n + 1) (G.f n b) = (F ≫ G).f (n + 1) z := by
  have hc := ConcreteCategory.congr_hom (G.comm n (n + 1)).symm b
  change G.f (n + 1) (D.d n (n + 1) b) = E.d n (n + 1) (G.f n b) at hc
  exact hc.symm.trans (congrArg (fun t => G.f (n + 1) t) h)

/-- Evaluation of a signed cochain-map square after an isomorphism lift. -/
private theorem supportConnecting_difference_of_iso_lift
    {M L R I D E : CochainComplex AddCommGrpCat.{0} ℕ}
    (left : M ⟶ L) (right : M ⟶ R)
    (leftIncl : L ⟶ E) (rightIncl : R ⟶ E) (intersectionIncl : I ⟶ E)
    (middle : M ⟶ D) (e : I ≅ D)
    (h : left ≫ leftIncl - right ≫ rightIncl = middle ≫ e.inv ≫ intersectionIncl)
    (n : ℕ) (b : M.X n) (a : I.X n) (hb : middle.f n b = e.hom.f n a) :
    leftIncl.f n (left.f n b) - rightIncl.f n (right.f n b) = intersectionIncl.f n a := by
  have he := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom h n) b
  change leftIncl.f n (left.f n b) - rightIncl.f n (right.f n b) =
    intersectionIncl.f n (e.inv.f n (middle.f n b)) at he
  rw [hb] at he
  have hi : e.inv.f n (e.hom.f n a) = a :=
    ConcreteCategory.congr_hom (HomologicalComplex.congr_hom e.hom_inv_id n) a
  rwa [hi] at he

/-- The signed component formula recovers the original relative cocycle. -/
private theorem supportConnecting_component_difference_value
    (X : TopCat.{0}) (A B : Set X) (n : ℕ)
    (a : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∩ B)) n)
    (b₂ : (SupportCohomologyMayerVietoris.binaryRelativeDualSequence X A B).X₂.X n)
    (hb₂ : (SupportCohomologyMayerVietoris.binaryRelativeDualSequence X A B).g.f n b₂ =
      (SupportCohomologyMayerVietoris.binaryRelativeDualSequence X A B).X₃.iCycles n
        (relativeDualCocycle X (A ∩ B) n a)) :
    (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f n
        ((supportConnectingLeftComponent X A B).f n b₂) -
      (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f n
        ((supportConnectingRightComponent X A B).f n b₂) =
      (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (A ∩ B)).f n a.val := by
  exact supportConnecting_difference_of_iso_lift
    (supportConnectingLeftComponent X A B) (supportConnectingRightComponent X A B)
    (RelativeCochainDual.rationalCochainsForget.map (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A))
    (RelativeCochainDual.rationalCochainsForget.map (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B))
    (RelativeCochainDual.rationalCochainsForget.map (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (A ∩ B)))
    (SupportCohomologyMayerVietoris.binaryRelativeDualSequence X A B).g (RelativeCochainDual.relativeCochainIntegralDualIso X (A ∩ B))
    (supportConnectingComponents_difference X A B) n b₂ a.val
    (hb₂.trans (relativeDualCocycle_val X (A ∩ B) n a))

/-- Concrete relative-cochain representatives for the actual Mayer–Vietoris
connecting class. The two cochains have the same differential, namely the
restriction of a genuine cocycle on the union. -/
theorem supportConnecting_components (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ)
    (a : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∩ B)) n) :
    ∃ (bA : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X n)
      (bB : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B).X n)
      (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)) (n + 1)),
      (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f n bA -
          (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f n bB =
        (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (A ∩ B)).f n a.val ∧
      (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).d n (n + 1) bA =
        (relativeRationalSubsetCochainMap X (Set.subset_union_left : A ⊆ A ∪ B)).f
          (n + 1) c.val ∧
      (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B).d n (n + 1) bB =
        (relativeRationalSubsetCochainMap X (Set.subset_union_right : B ⊆ A ∪ B)).f
          (n + 1) c.val ∧
      SupportCohomologyMayerVietoris.relativeRationalMayerVietorisBoundary X A B hA hB n
          (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∩ B)) n a) =
        Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)) (n + 1) c := by
  let S := SupportCohomologyMayerVietoris.binaryRelativeDualSequence X A B
  let C := Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)
  let T := RelativeCochainDual.rationalCochainsForget.obj C
  let x₃ : S.X₃.cycles n := relativeDualCocycle X (A ∩ B) n a
  obtain ⟨c₀, b₂, hb₂, hd, hclass⟩ :=
    supportConnecting_representatives X A B hA hB n x₃
  let bA := (supportConnectingLeftComponent X A B).f n b₂
  let bB := (supportConnectingRightComponent X A B).f n b₂
  let c := forgottenCycleToRationalCocycle C (n + 1) c₀
  refine ⟨bA, bB, c, ?_, ?_, ?_, ?_⟩
  · exact supportConnecting_component_difference_value X A B n a b₂ hb₂
  · have hc' := supportConnecting_component_differential_of_lift
      (binaryRelativeFirstEndpointMap X A B ≫ S.f)
      (supportConnectingLeftComponent X A B) n b₂ (T.iCycles (n + 1) c₀) hd
    have hf := ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom (supportConnectingLeftComponent_first X A B) (n + 1))
      (T.iCycles (n + 1) c₀)
    exact hc'.trans hf
  · have hc' := supportConnecting_component_differential_of_lift
      (binaryRelativeFirstEndpointMap X A B ≫ S.f)
      (supportConnectingRightComponent X A B) n b₂ (T.iCycles (n + 1) c₀) hd
    have hf := ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom (supportConnectingRightComponent_first X A B) (n + 1))
      (T.iCycles (n + 1) c₀)
    exact hc'.trans hf
  · have ha := relativeDualCocycle_class X (A ∩ B) n a
    change (SupportCohomologyMayerVietoris.binaryRelativeDualThirdHomologyIso X A B n).hom (S.X₃.homologyπ n x₃) =
      Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∩ B)) n a at ha
    rw [ha] at hclass
    exact hclass.symm.trans (forgottenCycleToRationalCocycle_class C (n + 1) c₀).symm

/-- The representative formula transports along genuine equalities of the
intersection and union subspaces. -/
theorem supportConnecting_components_congr (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) {I J : Set X}
    (hI : A ∩ B = I) (hJ : A ∪ B = J) (hAJ : A ⊆ J) (hBJ : B ⊆ J)
    (a : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X I) n) :
    ∃ (bA : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X n)
      (bB : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B).X n)
      (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X J) (n + 1)),
      (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f n bA -
          (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f n bB =
        (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X I).f n a.val ∧
      (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).d n (n + 1) bA =
        (relativeRationalSubsetCochainMap X hAJ).f (n + 1) c.val ∧
      (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B).d n (n + 1) bB =
        (relativeRationalSubsetCochainMap X hBJ).f (n + 1) c.val ∧
      ((SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr X hI n).inv ≫
          SupportCohomologyMayerVietoris.relativeRationalMayerVietorisBoundary X A B hA hB n ≫
          (SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr X hJ (n + 1)).hom)
          (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X I) n a) =
        Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X J) (n + 1) c := by
  subst I
  subst J
  simpa only [SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr, eqToIso_refl,
    Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id] using
    supportConnecting_components X A B hA hB n a

/-- The closed-support form of the representative theorem, using the exact
complement complexes and the native support connecting morphism. -/
theorem supportConnecting_components_support (X : TopCat.{0}) (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L) (n : ℕ)
    (a : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (K ∪ L)ᶜ) n) :
    ∃ (bK : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Kᶜ).X n)
      (bL : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Lᶜ).X n)
      (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (K ∩ L)ᶜ) (n + 1)),
      (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X Kᶜ).f n bK -
          (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X Lᶜ).f n bL =
        (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (K ∪ L)ᶜ).f n a.val ∧
      (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Kᶜ).d n (n + 1) bK =
        (relativeRationalSubsetCochainMap X
          (show Kᶜ ⊆ (K ∩ L)ᶜ from fun _ hx h => hx h.1)).f (n + 1) c.val ∧
      (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Lᶜ).d n (n + 1) bL =
        (relativeRationalSubsetCochainMap X
          (show Lᶜ ⊆ (K ∩ L)ᶜ from fun _ hx h => hx h.2)).f (n + 1) c.val ∧
      SupportCohomologyMayerVietoris.supportCohomologyMayerVietorisBoundary X K L hK hL n
          (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (K ∪ L)ᶜ) n a) =
        Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (K ∩ L)ᶜ) (n + 1) c := by
  simpa only [SupportCohomologyMayerVietoris.supportCohomologyMayerVietorisBoundary, SupportCohomologyMayerVietoris.supportUnionCohomologyIso,
    SupportCohomologyMayerVietoris.supportIntersectionCohomologyIso] using
    supportConnecting_components_congr X Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl n
      (Set.compl_union K L).symm (Set.compl_inter K L).symm
      (fun _ hx h => hx h.1) (fun _ hx h => hx h.2) a

end

end OAI.AlgebraicTopology.Duality.Poincare.SupportConnectingComponents
