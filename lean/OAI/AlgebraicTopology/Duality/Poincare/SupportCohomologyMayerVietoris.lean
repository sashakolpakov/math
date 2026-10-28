import OAI.AlgebraicTopology.Duality.Poincare.RelativeCochainDual
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportExcision
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportCohomology
import OAI.AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports
import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! # Support Cohomology Mayer Vietoris -/

namespace OAI.AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris

noncomputable section

/-!
# Rational cohomology Mayer--Vietoris with closed supports

The chain-level input is the exact sequence with the actual binary
small-chain quotient. Rational duality is exact because the rational
coefficient group is injective over the integers. The comparison with
ordinary relative chains uses the established subdivision quasi-isomorphism.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

open OAI.AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance : Injective RelativeCochainDual.rationalIntegralCoefficient := Cohomology.Singular.IntegralCoefficientInjective.injective_restrictScalars_rat

/-- Exact rational duality applied to a genuine short exact chain sequence. -/
theorem rationalChainDual_shortExact
    (S : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ)) (hS : S.ShortExact) :
    (S.op.map RelativeCochainDual.rationalChainDualFunctor).ShortExact := by
  apply (HomologicalComplex.shortExact_iff_degreewise_shortExact _).2
  intro n
  have h := ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n).op
  have := h.mono_f
  have := h.epi_g
  have hdual := h.map (preadditiveYonedaObj RelativeCochainDual.rationalIntegralCoefficient)
  have := hdual.mono_f
  have := hdual.epi_g
  exact hdual.map (forget₂ (ModuleCat (End RelativeCochainDual.rationalIntegralCoefficient)) AddCommGrpCat)

/-- The actual dual of the relative binary small-chain sequence. -/
def binaryRelativeDualSequence (X : TopCat.{0}) (A B : Set X) :
    ShortComplex (CochainComplex AddCommGrpCat.{0} ℕ) :=
  (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence X A B).op.map RelativeCochainDual.rationalChainDualFunctor

theorem binaryRelativeDualSequence_shortExact (X : TopCat.{0}) (A B : Set X) :
    (binaryRelativeDualSequence X A B).ShortExact :=
  rationalChainDual_shortExact _ (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence_shortExact X A B)

@[simp] theorem binaryRelativeDualSequence_f (X : TopCat.{0}) (A B : Set X) :
    (binaryRelativeDualSequence X A B).f =
      RelativeCochainDual.rationalChainDualMap (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence X A B).g := rfl

@[simp] theorem binaryRelativeDualSequence_g (X : TopCat.{0}) (A B : Set X) :
    (binaryRelativeDualSequence X A B).g =
      RelativeCochainDual.rationalChainDualMap (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence X A B).f := rfl

/-- The dual of an actual direct sum is the direct sum of its two duals. -/
def rationalChainDualBiprodIso (C D : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    RelativeCochainDual.rationalChainDual (C ⊞ D) ≅ RelativeCochainDual.rationalChainDual C ⊞ RelativeCochainDual.rationalChainDual D := by
  letI : PreservesBinaryBiproduct (op C) (op D) RelativeCochainDual.rationalChainDualFunctor :=
    preservesBinaryBiproduct_of_preservesBiproduct RelativeCochainDual.rationalChainDualFunctor _ _
  exact RelativeCochainDual.rationalChainDualFunctor.mapIso (biprod.opIso C D) ≪≫
    RelativeCochainDual.rationalChainDualFunctor.mapBiprod (op C) (op D)

@[reassoc (attr := simp)]
theorem rationalChainDualBiprodIso_hom_fst (C D : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    (rationalChainDualBiprodIso C D).hom ≫ biprod.fst =
      RelativeCochainDual.rationalChainDualMap (biprod.inl : C ⟶ C ⊞ D) := by
  simp only [rationalChainDualBiprodIso, Iso.trans_hom, Functor.mapIso_hom,
    Functor.mapBiprod_hom, Category.assoc, biprod.lift_fst]
  rw [← Functor.map_comp, biprod.opIso_hom_fst]

@[reassoc (attr := simp)]
theorem rationalChainDualBiprodIso_hom_snd (C D : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    (rationalChainDualBiprodIso C D).hom ≫ biprod.snd =
      RelativeCochainDual.rationalChainDualMap (biprod.inr : D ⟶ C ⊞ D) := by
  simp only [rationalChainDualBiprodIso, Iso.trans_hom, Functor.mapIso_hom,
    Functor.mapBiprod_hom, Category.assoc, biprod.lift_snd]
  rw [← Functor.map_comp, biprod.opIso_hom_snd]

/-- Forgetting rational scalars commutes with the actual cohomology object. -/
def rationalCochainHomologyForgetIso (C : CochainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ) :
    (RelativeCochainDual.rationalCochainsForget.obj C).homology n ≅
      (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).obj (C.homology n) :=
  (C.sc n).mapHomologyIso (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0})

@[reassoc]
theorem rationalCochainHomologyForgetIso_naturality
    {C D : CochainComplex (ModuleCat.{0} ℚ) ℕ} (f : C ⟶ D) (n : ℕ) :
    HomologicalComplex.homologyMap (RelativeCochainDual.rationalCochainsForget.map f) n ≫
        (rationalCochainHomologyForgetIso D n).hom =
      (rationalCochainHomologyForgetIso C n).hom ≫
        (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map
          (HomologicalComplex.homologyMap f n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map f)
    (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0})

@[reassoc]
theorem rationalCochainHomologyForgetIso_inv_naturality
    {C D : CochainComplex (ModuleCat.{0} ℚ) ℕ} (f : C ⟶ D) (n : ℕ) :
    (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map
        (HomologicalComplex.homologyMap f n) ≫
        (rationalCochainHomologyForgetIso D n).inv =
      (rationalCochainHomologyForgetIso C n).inv ≫
        HomologicalComplex.homologyMap (RelativeCochainDual.rationalCochainsForget.map f) n :=
  ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map f)
    (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0})

/-- The cohomology version of the actual relative cochain/integral-chain duality. -/
def relativeRationalCohomologyDualIso (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).obj
        (Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n) ≅
      (RelativeCochainDual.rationalChainDual (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A)).homology n :=
  (rationalCochainHomologyForgetIso
    (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) n).symm ≪≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (ComplexShape.up ℕ) n).mapIso
        (RelativeCochainDual.relativeCochainIntegralDualIso X A)

@[reassoc]
theorem relativeRationalCohomologyDualIso_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) (n : ℕ) :
    (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map
        (Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f h n) ≫
        (relativeRationalCohomologyDualIso X A n).hom =
      (relativeRationalCohomologyDualIso Y B n).hom ≫
        HomologicalComplex.homologyMap (RelativeCochainDual.rationalChainDualMap
          (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChainsMap f h)) n := by
  simp only [relativeRationalCohomologyDualIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, ← Category.assoc]
  rw [rationalCochainHomologyForgetIso_inv_naturality]
  simp only [Category.assoc]
  have hnat := congrArg
    (fun g => (HomologicalComplex.homologyFunctor AddCommGrpCat.{0}
      (ComplexShape.up ℕ) n).map g)
    (RelativeCochainDual.relativeCochainIntegralDualIso_naturality f h)
  simp only [Functor.map_comp] at hnat
  exact congrArg (fun g => (rationalCochainHomologyForgetIso
    (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) Y B) n).inv ≫ g) hnat

/-- The small-chain quotient computes the actual relative rational cohomology
of the union; the comparison uses the proved subdivision quasi-isomorphism. -/
def binaryRelativeDualFirstHomologyIso (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    (binaryRelativeDualSequence X A B).X₁.homology n ≅
      (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).obj
        (Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (A ∪ B) n) := by
  have : QuasiIso (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B) :=
    AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative_quasiIso X A B hA hB
  have : QuasiIso (RelativeCochainDual.rationalChainDualMap (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B)) :=
    CompactSupportExcision.rationalChainDualMap_quasiIso (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B)
  exact (isoOfQuasiIsoAt
    (RelativeCochainDual.rationalChainDualMap (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B)) n).symm ≪≫
      (relativeRationalCohomologyDualIso X (A ∪ B) n).symm

/-- The middle term is the actual direct sum of the two relative cohomology groups. -/
def binaryRelativeDualMiddleHomologyIso (X : TopCat.{0}) (A B : Set X) (n : ℕ) :
    (binaryRelativeDualSequence X A B).X₂.homology n ≅
      (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).obj
        (Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n ⊞
          Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B n) := by
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (ComplexShape.up ℕ) n
  let F := forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}
  letI : PreservesBinaryBiproduct
      (RelativeCochainDual.rationalChainDual (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A))
      (RelativeCochainDual.rationalChainDual (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B)) H :=
    preservesBinaryBiproduct_of_preservesBiproduct H _ _
  letI : PreservesBinaryBiproduct
      (Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n)
      (Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B n) F :=
    preservesBinaryBiproduct_of_preservesBiproduct F _ _
  exact H.mapIso (rationalChainDualBiprodIso
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B)) ≪≫
    H.mapBiprod _ _ ≪≫
    biprod.mapIso (relativeRationalCohomologyDualIso X A n).symm
      (relativeRationalCohomologyDualIso X B n).symm ≪≫
    (F.mapBiprod _ _).symm

/-- The third dual term is ordinary relative rational cohomology of the intersection. -/
abbrev binaryRelativeDualThirdHomologyIso (X : TopCat.{0}) (A B : Set X) (n : ℕ) :
    (binaryRelativeDualSequence X A B).X₃.homology n ≅
      (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).obj
        (Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (A ∩ B) n) :=
  (relativeRationalCohomologyDualIso X (A ∩ B) n).symm

@[reassoc (attr := simp)]
theorem rationalChainDualBiprodIso_inl_inv (C D : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    biprod.inl ≫ (rationalChainDualBiprodIso C D).inv =
      RelativeCochainDual.rationalChainDualMap (biprod.fst : C ⊞ D ⟶ C) := by
  simp only [rationalChainDualBiprodIso, Iso.trans_inv, Functor.mapIso_inv,
    Functor.mapBiprod_inv, biprod.inl_desc_assoc]
  rw [← Functor.map_comp, biprod.inl_opIso_inv]

@[reassoc (attr := simp)]
theorem rationalChainDualBiprodIso_inr_inv (C D : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    biprod.inr ≫ (rationalChainDualBiprodIso C D).inv =
      RelativeCochainDual.rationalChainDualMap (biprod.snd : C ⊞ D ⟶ D) := by
  simp only [rationalChainDualBiprodIso, Iso.trans_inv, Functor.mapIso_inv,
    Functor.mapBiprod_inv, biprod.inr_desc_assoc]
  rw [← Functor.map_comp, biprod.inr_opIso_inv]

@[reassoc (attr := simp)]
theorem binaryRelativeDualMiddleHomologyIso_hom_fst (X : TopCat.{0})
    (A B : Set X) (n : ℕ) :
    (binaryRelativeDualMiddleHomologyIso X A B n).hom ≫
        (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map biprod.fst =
      HomologicalComplex.homologyMap (RelativeCochainDual.rationalChainDualMap
        (biprod.inl : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A ⟶
          AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A ⊞ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B)) n ≫
        (relativeRationalCohomologyDualIso X A n).inv := by
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (ComplexShape.up ℕ) n
  let F := forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}
  let QA := Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n
  let QB := Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B n
  let DA := RelativeCochainDual.rationalChainDual (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A)
  let DB := RelativeCochainDual.rationalChainDual (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B)
  let : PreservesBinaryBiproduct QA QB F :=
    preservesBinaryBiproduct_of_preservesBiproduct F _ _
  let : PreservesBinaryBiproduct DA DB H :=
    preservesBinaryBiproduct_of_preservesBiproduct H _ _
  let eA : F.obj QA ≅ H.obj DA := relativeRationalCohomologyDualIso X A n
  let eB : F.obj QB ≅ H.obj DB := relativeRationalCohomologyDualIso X B n
  have hF : (F.mapBiprod QA QB).inv ≫ F.map biprod.fst = biprod.fst := by
    apply (cancel_epi (F.mapBiprod QA QB).hom).1
    rw [Iso.hom_inv_id_assoc]
    exact (biprod.lift_fst _ _).symm
  change (H.map (rationalChainDualBiprodIso (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A)
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B)).hom ≫ (H.mapBiprod DA DB).hom ≫
      biprod.map eA.inv
        eB.inv ≫
      (F.mapBiprod QA QB).inv) ≫ F.map biprod.fst =
    H.map (RelativeCochainDual.rationalChainDualMap biprod.inl) ≫
      eA.inv
  simp only [Category.assoc, hF, biprod.map_fst, Functor.mapBiprod_hom,
    biprod.lift_fst_assoc]
  rw [← Category.assoc, ← Functor.map_comp, rationalChainDualBiprodIso_hom_fst]

@[reassoc (attr := simp)]
theorem binaryRelativeDualMiddleHomologyIso_hom_snd (X : TopCat.{0})
    (A B : Set X) (n : ℕ) :
    (binaryRelativeDualMiddleHomologyIso X A B n).hom ≫
        (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map biprod.snd =
      HomologicalComplex.homologyMap (RelativeCochainDual.rationalChainDualMap
        (biprod.inr : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B ⟶
          AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A ⊞ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B)) n ≫
        (relativeRationalCohomologyDualIso X B n).inv := by
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (ComplexShape.up ℕ) n
  let F := forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}
  let QA := Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n
  let QB := Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B n
  let DA := RelativeCochainDual.rationalChainDual (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A)
  let DB := RelativeCochainDual.rationalChainDual (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B)
  let : PreservesBinaryBiproduct QA QB F :=
    preservesBinaryBiproduct_of_preservesBiproduct F _ _
  let : PreservesBinaryBiproduct DA DB H :=
    preservesBinaryBiproduct_of_preservesBiproduct H _ _
  let eA : F.obj QA ≅ H.obj DA := relativeRationalCohomologyDualIso X A n
  let eB : F.obj QB ≅ H.obj DB := relativeRationalCohomologyDualIso X B n
  have hF : (F.mapBiprod QA QB).inv ≫ F.map biprod.snd = biprod.snd := by
    apply (cancel_epi (F.mapBiprod QA QB).hom).1
    rw [Iso.hom_inv_id_assoc]
    exact (biprod.lift_snd _ _).symm
  change (H.map (rationalChainDualBiprodIso (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A)
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B)).hom ≫ (H.mapBiprod DA DB).hom ≫
      biprod.map eA.inv
        eB.inv ≫
      (F.mapBiprod QA QB).inv) ≫ F.map biprod.snd =
    H.map (RelativeCochainDual.rationalChainDualMap biprod.inr) ≫
      eB.inv
  simp only [Category.assoc, hF, biprod.map_snd, Functor.mapBiprod_hom,
    biprod.lift_snd_assoc]
  rw [← Category.assoc, ← Functor.map_comp, rationalChainDualBiprodIso_hom_snd]

@[reassoc (attr := simp)]
theorem binaryRelativeDualMiddleHomologyIso_inl_inv (X : TopCat.{0})
    (A B : Set X) (n : ℕ) :
    (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map biprod.inl ≫
        (binaryRelativeDualMiddleHomologyIso X A B n).inv =
      (relativeRationalCohomologyDualIso X A n).hom ≫
        HomologicalComplex.homologyMap (RelativeCochainDual.rationalChainDualMap
          (biprod.fst : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A ⊞ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B ⟶
            AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A)) n := by
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (ComplexShape.up ℕ) n
  let F := forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}
  let QA := Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n
  let QB := Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B n
  let DA := RelativeCochainDual.rationalChainDual (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A)
  let DB := RelativeCochainDual.rationalChainDual (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B)
  let : PreservesBinaryBiproduct QA QB F :=
    preservesBinaryBiproduct_of_preservesBiproduct F _ _
  let : PreservesBinaryBiproduct DA DB H :=
    preservesBinaryBiproduct_of_preservesBiproduct H _ _
  let eA : F.obj QA ≅ H.obj DA := relativeRationalCohomologyDualIso X A n
  let eB : F.obj QB ≅ H.obj DB := relativeRationalCohomologyDualIso X B n
  have hF : F.map biprod.inl ≫ (F.mapBiprod QA QB).hom = biprod.inl := by
    apply (cancel_mono (F.mapBiprod QA QB).inv).1
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact (biprod.inl_desc _ _).symm
  change F.map biprod.inl ≫ ((F.mapBiprod QA QB).hom ≫
      biprod.map eA.hom
        eB.hom ≫
      (H.mapBiprod DA DB).inv ≫
      H.map (rationalChainDualBiprodIso (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A)
        (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B)).inv) =
    eA.hom ≫
      H.map (RelativeCochainDual.rationalChainDualMap biprod.fst)
  rw [← Category.assoc, hF]
  simp only [biprod.inl_map_assoc, Functor.mapBiprod_inv, biprod.inl_desc_assoc]
  rw [← Functor.map_comp, rationalChainDualBiprodIso_inl_inv]

@[reassoc (attr := simp)]
theorem binaryRelativeDualMiddleHomologyIso_inr_inv (X : TopCat.{0})
    (A B : Set X) (n : ℕ) :
    (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map biprod.inr ≫
        (binaryRelativeDualMiddleHomologyIso X A B n).inv =
      (relativeRationalCohomologyDualIso X B n).hom ≫
        HomologicalComplex.homologyMap (RelativeCochainDual.rationalChainDualMap
          (biprod.snd : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A ⊞ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B ⟶
            AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B)) n := by
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (ComplexShape.up ℕ) n
  let F := forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}
  let QA := Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n
  let QB := Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B n
  let DA := RelativeCochainDual.rationalChainDual (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A)
  let DB := RelativeCochainDual.rationalChainDual (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B)
  let : PreservesBinaryBiproduct QA QB F :=
    preservesBinaryBiproduct_of_preservesBiproduct F _ _
  let : PreservesBinaryBiproduct DA DB H :=
    preservesBinaryBiproduct_of_preservesBiproduct H _ _
  let eA : F.obj QA ≅ H.obj DA := relativeRationalCohomologyDualIso X A n
  let eB : F.obj QB ≅ H.obj DB := relativeRationalCohomologyDualIso X B n
  have hF : F.map biprod.inr ≫ (F.mapBiprod QA QB).hom = biprod.inr := by
    apply (cancel_mono (F.mapBiprod QA QB).inv).1
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact (biprod.inr_desc _ _).symm
  change F.map biprod.inr ≫ ((F.mapBiprod QA QB).hom ≫
      biprod.map eA.hom
        eB.hom ≫
      (H.mapBiprod DA DB).inv ≫
      H.map (rationalChainDualBiprodIso (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A)
        (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B)).inv) =
    eB.hom ≫
      H.map (RelativeCochainDual.rationalChainDualMap biprod.snd)
  rw [← Category.assoc, hF]
  simp only [biprod.inr_map_assoc, Functor.mapBiprod_inv, biprod.inr_desc_assoc]
  rw [← Functor.map_comp, rationalChainDualBiprodIso_inr_inv]

@[reassoc (attr := simp)]
theorem binaryRelativeDualFirstHomologyIso_inv (X : TopCat.{0})
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    (binaryRelativeDualFirstHomologyIso X A B hA hB n).inv =
      (relativeRationalCohomologyDualIso X (A ∪ B) n).hom ≫
        HomologicalComplex.homologyMap
          (RelativeCochainDual.rationalChainDualMap (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B)) n := rfl

/-- Restriction for an inclusion of actual relative pairs. -/
abbrev relativeRationalSubsetCohomologyMap (X : TopCat.{0}) {A B : Set X}
    (h : A ⊆ B) (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B n ⟶
      Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n :=
  Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 X) (fun _ hx => h hx) n

@[reassoc]
theorem relativeRationalSubsetCohomologyMap_conjugate (X : TopCat.{0})
    {A B : Set X} (h : A ⊆ B) (n : ℕ) :
    (relativeRationalCohomologyDualIso X B n).hom ≫
        HomologicalComplex.homologyMap (RelativeCochainDual.rationalChainDualMap
          (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X h)) n ≫
        (relativeRationalCohomologyDualIso X A n).inv =
      (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map
        (relativeRationalSubsetCohomologyMap X h n) := by
  have hn := congrArg (fun f => f ≫ (relativeRationalCohomologyDualIso X A n).inv)
    (relativeRationalCohomologyDualIso_naturality (𝟙 X) (fun _ hx => h hx) n)
  simpa only [AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap, relativeRationalSubsetCohomologyMap,
    Category.assoc, Iso.hom_inv_id, Category.comp_id] using hn.symm

/-- The first relative cohomology map is the pair of the two restriction maps. -/
def relativeRationalMayerVietorisFirst (X : TopCat.{0}) (A B : Set X) (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (A ∪ B) n ⟶
      Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n ⊞
        Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B n :=
  biprod.lift (relativeRationalSubsetCohomologyMap X Set.subset_union_left n)
    (relativeRationalSubsetCohomologyMap X Set.subset_union_right n)

/-- The second relative cohomology map is the difference of restrictions. -/
def relativeRationalMayerVietorisSecond (X : TopCat.{0}) (A B : Set X) (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n ⊞
        Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B n ⟶
      Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (A ∩ B) n :=
  biprod.desc (relativeRationalSubsetCohomologyMap X Set.inter_subset_left n)
    (-relativeRationalSubsetCohomologyMap X Set.inter_subset_right n)

@[reassoc (attr := simp)]
theorem relativeRationalMayerVietorisFirst_fst (X : TopCat.{0}) (A B : Set X) (n : ℕ) :
    relativeRationalMayerVietorisFirst X A B n ≫ biprod.fst =
      relativeRationalSubsetCohomologyMap X Set.subset_union_left n :=
  biprod.lift_fst _ _

@[reassoc (attr := simp)]
theorem relativeRationalMayerVietorisFirst_snd (X : TopCat.{0}) (A B : Set X) (n : ℕ) :
    relativeRationalMayerVietorisFirst X A B n ≫ biprod.snd =
      relativeRationalSubsetCohomologyMap X Set.subset_union_right n :=
  biprod.lift_snd _ _

@[reassoc (attr := simp)]
theorem relativeRationalMayerVietorisSecond_inl (X : TopCat.{0}) (A B : Set X) (n : ℕ) :
    biprod.inl ≫ relativeRationalMayerVietorisSecond X A B n =
      relativeRationalSubsetCohomologyMap X Set.inter_subset_left n :=
  biprod.inl_desc _ _

@[reassoc (attr := simp)]
theorem relativeRationalMayerVietorisSecond_inr (X : TopCat.{0}) (A B : Set X) (n : ℕ) :
    biprod.inr ≫ relativeRationalMayerVietorisSecond X A B n =
      -relativeRationalSubsetCohomologyMap X Set.inter_subset_right n :=
  biprod.inr_desc _ _

private theorem rationalBiprod_hom_ext {P Q : ModuleCat.{0} ℚ} {Z : AddCommGrpCat.{0}}
    (f g : Z ⟶ (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).obj (P ⊞ Q))
    (hf : f ≫ (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map biprod.fst =
      g ≫ (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map biprod.fst)
    (hg : f ≫ (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map biprod.snd =
      g ≫ (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map biprod.snd) : f = g := by
  let F := forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}
  let : PreservesBinaryBiproduct P Q F :=
    preservesBinaryBiproduct_of_preservesBiproduct F _ _
  apply (cancel_mono (F.mapBiprod P Q).hom).1
  apply biprod.hom_ext
  · simpa only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_fst] using hf
  · simpa only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_snd] using hg

private theorem rationalBiprod_hom_ext' {P Q : ModuleCat.{0} ℚ} {Z : AddCommGrpCat.{0}}
    (f g : (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).obj (P ⊞ Q) ⟶ Z)
    (hf : (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map biprod.inl ≫ f =
      (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map biprod.inl ≫ g)
    (hg : (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map biprod.inr ≫ f =
      (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map biprod.inr ≫ g) : f = g := by
  let F := forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}
  let : PreservesBinaryBiproduct P Q F :=
    preservesBinaryBiproduct_of_preservesBiproduct F _ _
  apply (cancel_epi (F.mapBiprod P Q).inv).1
  apply biprod.hom_ext'
  · simpa only [Functor.mapBiprod_inv, biprod.inl_desc_assoc] using hf
  · simpa only [Functor.mapBiprod_inv, biprod.inr_desc_assoc] using hg

@[simp]
theorem rationalChainDualMap_neg {C D : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : C ⟶ D) : RelativeCochainDual.rationalChainDualMap (-f) = -RelativeCochainDual.rationalChainDualMap f := by
  change RelativeCochainDual.rationalChainDualFunctor.map ((-f).op) = -RelativeCochainDual.rationalChainDualFunctor.map f.op
  rw [op_neg, Functor.map_neg]

/-- The exact-sequence first map is precisely the two actual restriction maps. -/
theorem binaryRelativeDualFirstHomologyIso_first (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    (binaryRelativeDualFirstHomologyIso X A B hA hB n).inv ≫
      HomologicalComplex.homologyMap (binaryRelativeDualSequence X A B).f n ≫
      (binaryRelativeDualMiddleHomologyIso X A B n).hom =
    (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map
      (relativeRationalMayerVietorisFirst X A B n) := by
  apply rationalBiprod_hom_ext
  · simp only [Category.assoc, binaryRelativeDualMiddleHomologyIso_hom_fst,
      ← Functor.map_comp, relativeRationalMayerVietorisFirst_fst]
    have hc : (biprod.inl : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A ⟶
        AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A ⊞ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B) ≫
        (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence X A B).g ≫
        AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B =
        AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X Set.subset_union_left := by
      simp [AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence]
    have hd := congrArg (fun f => HomologicalComplex.homologyMap
      (RelativeCochainDual.rationalChainDualMap f) n) hc
    simp only [RelativeCochainDual.rationalChainDualMap_comp, HomologicalComplex.homologyMap_comp,
      Category.assoc] at hd
    have ht := congrArg (fun f => (relativeRationalCohomologyDualIso X (A ∪ B) n).hom ≫
      f ≫ (relativeRationalCohomologyDualIso X A n).inv) hd
    have hh := ht.trans (relativeRationalSubsetCohomologyMap_conjugate X
      Set.subset_union_left n)
    simpa only [binaryRelativeDualFirstHomologyIso_inv, binaryRelativeDualSequence_f,
      Category.assoc] using hh
  · simp only [Category.assoc, binaryRelativeDualMiddleHomologyIso_hom_snd,
      ← Functor.map_comp, relativeRationalMayerVietorisFirst_snd]
    have hc : (biprod.inr : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B ⟶
        AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A ⊞ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B) ≫
        (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence X A B).g ≫
        AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B =
        AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X Set.subset_union_right := by
      simp [AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence]
    have hd := congrArg (fun f => HomologicalComplex.homologyMap
      (RelativeCochainDual.rationalChainDualMap f) n) hc
    simp only [RelativeCochainDual.rationalChainDualMap_comp, HomologicalComplex.homologyMap_comp,
      Category.assoc] at hd
    have ht := congrArg (fun f => (relativeRationalCohomologyDualIso X (A ∪ B) n).hom ≫
      f ≫ (relativeRationalCohomologyDualIso X B n).inv) hd
    have hh := ht.trans (relativeRationalSubsetCohomologyMap_conjugate X
      Set.subset_union_right n)
    simpa only [binaryRelativeDualFirstHomologyIso_inv, binaryRelativeDualSequence_f,
      Category.assoc] using hh

/-- The exact-sequence second map is precisely the difference of actual restrictions. -/
theorem binaryRelativeDualMiddleHomologyIso_second (X : TopCat.{0}) (A B : Set X)
    (n : ℕ) :
    (binaryRelativeDualMiddleHomologyIso X A B n).inv ≫
      HomologicalComplex.homologyMap (binaryRelativeDualSequence X A B).g n ≫
      (binaryRelativeDualThirdHomologyIso X A B n).hom =
    (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map
      (relativeRationalMayerVietorisSecond X A B n) := by
  apply rationalBiprod_hom_ext'
  · simp only [← Category.assoc, binaryRelativeDualMiddleHomologyIso_inl_inv,
      ← Functor.map_comp, relativeRationalMayerVietorisSecond_inl]
    have hc : (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence X A B).f ≫
        (biprod.fst : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A ⊞ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B ⟶
          AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) =
        AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X Set.inter_subset_left := by
      simp [AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence]
    have hd := congrArg (fun f => HomologicalComplex.homologyMap
      (RelativeCochainDual.rationalChainDualMap f) n) hc
    simp only [RelativeCochainDual.rationalChainDualMap_comp, HomologicalComplex.homologyMap_comp] at hd
    have ht := congrArg (fun f => (relativeRationalCohomologyDualIso X A n).hom ≫
      f ≫ (relativeRationalCohomologyDualIso X (A ∩ B) n).inv) hd
    have hh := ht.trans (relativeRationalSubsetCohomologyMap_conjugate X
      Set.inter_subset_left n)
    simpa only [Category.assoc, binaryRelativeDualSequence_g,
      binaryRelativeDualThirdHomologyIso, Iso.symm_hom] using hh
  · simp only [← Category.assoc, binaryRelativeDualMiddleHomologyIso_inr_inv,
      ← Functor.map_comp, relativeRationalMayerVietorisSecond_inr]
    have hc : (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence X A B).f ≫
        (biprod.snd : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A ⊞ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B ⟶
          AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B) =
        -AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X Set.inter_subset_right := by
      simp [AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence]
    have hd := congrArg (fun f => HomologicalComplex.homologyMap
      (RelativeCochainDual.rationalChainDualMap f) n) hc
    simp only [RelativeCochainDual.rationalChainDualMap_comp, HomologicalComplex.homologyMap_comp,
      rationalChainDualMap_neg, HomologicalComplex.homologyMap_neg] at hd
    have ht := congrArg (fun f => (relativeRationalCohomologyDualIso X B n).hom ≫
      f ≫ (relativeRationalCohomologyDualIso X (A ∩ B) n).inv) hd
    simp only [Preadditive.neg_comp, Preadditive.comp_neg,
      relativeRationalSubsetCohomologyMap_conjugate] at ht
    simpa only [Category.assoc, Functor.map_neg, binaryRelativeDualSequence_g,
      binaryRelativeDualThirdHomologyIso, Iso.symm_hom] using ht

/-- An additive map of rational vector spaces is canonically rational-linear. -/
def rationalAdditiveHom {P Q : ModuleCat.{0} ℚ}
    (f : (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).obj P ⟶
      (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).obj Q) : P ⟶ Q :=
  ModuleCat.ofHom (show P →+ Q from f.hom).toRatLinearMap

@[simp]
theorem forget_rationalAdditiveHom {P Q : ModuleCat.{0} ℚ}
    (f : (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).obj P ⟶
      (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).obj Q) :
    (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map (rationalAdditiveHom f) = f := rfl

/-- The connecting map comes from the genuine dual short exact sequence and
its proved comparison with ordinary relative cohomology. -/
def relativeRationalMayerVietorisBoundary (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (A ∩ B) n ⟶
      Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (A ∪ B) (n + 1) :=
  rationalAdditiveHom ((binaryRelativeDualThirdHomologyIso X A B n).inv ≫
    (binaryRelativeDualSequence_shortExact X A B).δ n (n + 1) rfl ≫
    (binaryRelativeDualFirstHomologyIso X A B hA hB (n + 1)).hom)

@[reassoc (attr := simp)]
theorem relativeRationalMayerVietorisBoundary_forget (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map
        (relativeRationalMayerVietorisBoundary X A B hA hB n) =
      (binaryRelativeDualThirdHomologyIso X A B n).inv ≫
        (binaryRelativeDualSequence_shortExact X A B).δ n (n + 1) rfl ≫
        (binaryRelativeDualFirstHomologyIso X A B hA hB (n + 1)).hom := rfl

/-- Six consecutive terms of the actual rational relative-cohomology sequence. -/
def relativeRationalMayerVietorisSequence (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    ComposableArrows (ModuleCat.{0} ℚ) 5 :=
  ComposableArrows.mk₅ (relativeRationalMayerVietorisFirst X A B n)
    (relativeRationalMayerVietorisSecond X A B n)
    (relativeRationalMayerVietorisBoundary X A B hA hB n)
    (relativeRationalMayerVietorisFirst X A B (n + 1))
    (relativeRationalMayerVietorisSecond X A B (n + 1))

/-- Every object and map is identified with the native homology sequence. -/
def relativeRationalMayerVietorisSequenceIso (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    HomologicalComplex.HomologySequence.composableArrows₅
        (binaryRelativeDualSequence_shortExact X A B) n (n + 1) rfl ≅
      ((forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).mapComposableArrows 5).obj
        (relativeRationalMayerVietorisSequence X A B hA hB n) := by
  refine ComposableArrows.isoMk₅
    (binaryRelativeDualFirstHomologyIso X A B hA hB n)
    (binaryRelativeDualMiddleHomologyIso X A B n)
    (binaryRelativeDualThirdHomologyIso X A B n)
    (binaryRelativeDualFirstHomologyIso X A B hA hB (n + 1))
    (binaryRelativeDualMiddleHomologyIso X A B (n + 1))
    (binaryRelativeDualThirdHomologyIso X A B (n + 1)) ?_ ?_ ?_ ?_ ?_
  · change HomologicalComplex.homologyMap (binaryRelativeDualSequence X A B).f n ≫
        (binaryRelativeDualMiddleHomologyIso X A B n).hom =
      (binaryRelativeDualFirstHomologyIso X A B hA hB n).hom ≫
        (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map
          (relativeRationalMayerVietorisFirst X A B n)
    rw [← binaryRelativeDualFirstHomologyIso_first X A B hA hB n, Iso.hom_inv_id_assoc]
  · change HomologicalComplex.homologyMap (binaryRelativeDualSequence X A B).g n ≫
        (binaryRelativeDualThirdHomologyIso X A B n).hom =
      (binaryRelativeDualMiddleHomologyIso X A B n).hom ≫
        (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map
          (relativeRationalMayerVietorisSecond X A B n)
    rw [← binaryRelativeDualMiddleHomologyIso_second, Iso.hom_inv_id_assoc]
  · change (binaryRelativeDualSequence_shortExact X A B).δ n (n + 1) rfl ≫
        (binaryRelativeDualFirstHomologyIso X A B hA hB (n + 1)).hom =
      (binaryRelativeDualThirdHomologyIso X A B n).hom ≫
        (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map
          (relativeRationalMayerVietorisBoundary X A B hA hB n)
    rw [relativeRationalMayerVietorisBoundary_forget, Iso.hom_inv_id_assoc]
  · change HomologicalComplex.homologyMap (binaryRelativeDualSequence X A B).f (n + 1) ≫
        (binaryRelativeDualMiddleHomologyIso X A B (n + 1)).hom =
      (binaryRelativeDualFirstHomologyIso X A B hA hB (n + 1)).hom ≫
        (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map
          (relativeRationalMayerVietorisFirst X A B (n + 1))
    rw [← binaryRelativeDualFirstHomologyIso_first X A B hA hB (n + 1), Iso.hom_inv_id_assoc]
  · change HomologicalComplex.homologyMap (binaryRelativeDualSequence X A B).g (n + 1) ≫
        (binaryRelativeDualThirdHomologyIso X A B (n + 1)).hom =
      (binaryRelativeDualMiddleHomologyIso X A B (n + 1)).hom ≫
        (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map
          (relativeRationalMayerVietorisSecond X A B (n + 1))
    rw [← binaryRelativeDualMiddleHomologyIso_second, Iso.hom_inv_id_assoc]

private theorem rationalSequence_exact_of_forget_exact {n : ℕ}
    (S : ComposableArrows (ModuleCat.{0} ℚ) n)
    (hS : (((forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).mapComposableArrows n).obj S).Exact) :
    S.Exact where
  zero i hi := by
    apply (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map_injective
    rw [Functor.map_comp, Functor.map_zero]
    exact hS.zero i hi
  exact i hi := by
    apply (ShortComplex.exact_map_iff_of_faithful _
      (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0})).mp
    exact hS.exact i hi

/-- Rational relative Mayer--Vietoris, with exactness proved from actual
small chains and the injectivity of the rational coefficient group. -/
theorem relativeRationalMayerVietorisSequence_exact (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    (relativeRationalMayerVietorisSequence X A B hA hB n).Exact :=
  rationalSequence_exact_of_forget_exact _
    (ComposableArrows.exact_of_iso (relativeRationalMayerVietorisSequenceIso X A B hA hB n)
      (HomologicalComplex.HomologySequence.composableArrows₅_exact
        (binaryRelativeDualSequence_shortExact X A B) n (n + 1) rfl))

/-- Exactness at the direct sum of the relative cohomology groups. -/
theorem relativeRationalMayerVietoris_range_first (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    LinearMap.range (relativeRationalMayerVietorisFirst X A B n).hom =
      LinearMap.ker (relativeRationalMayerVietorisSecond X A B n).hom :=
  ((relativeRationalMayerVietorisSequence_exact X A B hA hB n).exact 0).moduleCat_range_eq_ker

/-- Exactness before the connecting map. -/
theorem relativeRationalMayerVietoris_range_second (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    LinearMap.range (relativeRationalMayerVietorisSecond X A B n).hom =
      LinearMap.ker (relativeRationalMayerVietorisBoundary X A B hA hB n).hom :=
  ((relativeRationalMayerVietorisSequence_exact X A B hA hB n).exact 1).moduleCat_range_eq_ker

/-- Exactness after the connecting map. -/
theorem relativeRationalMayerVietoris_range_boundary (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    LinearMap.range (relativeRationalMayerVietorisBoundary X A B hA hB n).hom =
      LinearMap.ker (relativeRationalMayerVietorisFirst X A B (n + 1)).hom :=
  ((relativeRationalMayerVietorisSequence_exact X A B hA hB n).exact 2).moduleCat_range_eq_ker

@[simp]
theorem relativeRationalSubsetCohomologyMap_refl (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    relativeRationalSubsetCohomologyMap X (Set.Subset.refl A) n = 𝟙 _ := by
  have hc : Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) (𝟙 X)
      (show Set.MapsTo (𝟙 X) A A from fun _ hx => hx) = 𝟙 _ := by
    apply (cancel_mono (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A)).1
    simp only [Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality, Cohomology.Singular.Functor.singularPullback_id,
      Category.comp_id, Category.id_comp]
  change HomologicalComplex.homologyMap _ n = _
  rw [hc, HomologicalComplex.homologyMap_id]

@[reassoc (attr := simp)]
theorem relativeRationalSubsetCohomologyMap_comp (X : TopCat.{0})
    {A B C : Set X} (h : A ⊆ B) (h' : B ⊆ C) (n : ℕ) :
    relativeRationalSubsetCohomologyMap X h' n ≫
        relativeRationalSubsetCohomologyMap X h n =
      relativeRationalSubsetCohomologyMap X (h.trans h') n := by
  have hc : Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) (𝟙 X)
      (show Set.MapsTo (𝟙 X) B C from fun _ hx => h' hx) ≫
      Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) (𝟙 X)
        (show Set.MapsTo (𝟙 X) A B from fun _ hx => h hx) =
      Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) (𝟙 X)
        (show Set.MapsTo (𝟙 X) A C from fun _ hx => h' (h hx)) := by
    apply (cancel_mono (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A)).1
    simp only [Category.assoc, Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality,
      Cohomology.Singular.Functor.singularPullback_id, Category.comp_id]
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n = _
  rw [← HomologicalComplex.homologyMap_comp, hc]

/-- Equality of the actual relative subspace transports its cohomology. -/
def relativeRationalCohomologyCongr (X : TopCat.{0}) {A B : Set X} (e : A = B) (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n ≅
      Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B n :=
  eqToIso (congrArg (fun S => Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S n) e)

@[reassoc]
theorem relativeRationalSubsetCohomologyMap_source_congr (X : TopCat.{0})
    {A B B' : Set X} (e : B = B') (h : A ⊆ B) (h' : A ⊆ B') (n : ℕ) :
    (relativeRationalCohomologyCongr X e n).hom ≫
        relativeRationalSubsetCohomologyMap X h' n =
      relativeRationalSubsetCohomologyMap X h n := by
  subst B'
  exact Category.id_comp _

@[reassoc]
theorem relativeRationalSubsetCohomologyMap_target_congr (X : TopCat.{0})
    {A A' B : Set X} (e : A = A') (h : A ⊆ B) (h' : A' ⊆ B) (n : ℕ) :
    relativeRationalSubsetCohomologyMap X h n ≫
        (relativeRationalCohomologyCongr X e n).hom =
      relativeRationalSubsetCohomologyMap X h' n := by
  subst A'
  exact Category.comp_id _

/-- Rational cohomology with support is the actual relative cohomology of
its complement, with no alternate cochain complex or support predicate. -/
abbrev rationalSupportCohomology (X : TopCat.{0}) (K : Set X) (n : ℕ) : ModuleCat.{0} ℚ :=
  Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X Kᶜ n

/-- Enlarging the support is the native relative-cohomology map of the two complements. -/
def supportCohomologyEnlargement (X : TopCat.{0}) {K L : Set X} (h : K ⊆ L) (n : ℕ) :
    rationalSupportCohomology X K n ⟶ rationalSupportCohomology X L n :=
  relativeRationalSubsetCohomologyMap X
    (show Lᶜ ⊆ Kᶜ from fun _ hx hxK => hx (h hxK)) n

@[simp]
theorem supportCohomologyEnlargement_refl (X : TopCat.{0}) (K : Set X) (n : ℕ) :
    supportCohomologyEnlargement X (Set.Subset.refl K) n = 𝟙 _ :=
  relativeRationalSubsetCohomologyMap_refl X Kᶜ n

@[reassoc (attr := simp)]
theorem supportCohomologyEnlargement_comp (X : TopCat.{0})
    {K L N : Set X} (h : K ⊆ L) (h' : L ⊆ N) (n : ℕ) :
    supportCohomologyEnlargement X h n ≫ supportCohomologyEnlargement X h' n =
      supportCohomologyEnlargement X (h.trans h') n :=
  relativeRationalSubsetCohomologyMap_comp X
    (show Nᶜ ⊆ Lᶜ from fun _ hx hxL => hx (h' hxL))
    (show Lᶜ ⊆ Kᶜ from fun _ hx hxK => hx (h hxK)) n

/-- Compatibility with the already constructed genuine compact-support diagram. -/
theorem supportCohomologyEnlargement_compact (X : TopCat.{0})
    {K L : TopologicalSpace.Compacts X} (h : K ≤ L) (n : ℕ) :
    supportCohomologyEnlargement X (show (K : Set X) ⊆ L from h) n =
      (CompactSupportCohomology.compactSupportCohomologyDiagram (ModuleCat.of ℚ ℚ) X n).map (homOfLE h) := rfl

/-- De Morgan's law identifies the first relative term with intersection support. -/
def supportIntersectionCohomologyIso (X : TopCat.{0}) (K L : Set X) (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (Kᶜ ∪ Lᶜ) n ≅
      rationalSupportCohomology X (K ∩ L) n :=
  relativeRationalCohomologyCongr X (Set.compl_inter K L).symm n

/-- De Morgan's law identifies the third relative term with union support. -/
def supportUnionCohomologyIso (X : TopCat.{0}) (K L : Set X) (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (Kᶜ ∩ Lᶜ) n ≅
      rationalSupportCohomology X (K ∪ L) n :=
  relativeRationalCohomologyCongr X (Set.compl_union K L).symm n

/-- The first support map consists of the two actual support enlargements. -/
def supportCohomologyMayerVietorisFirst (X : TopCat.{0}) (K L : Set X) (n : ℕ) :
    rationalSupportCohomology X (K ∩ L) n ⟶
      rationalSupportCohomology X K n ⊞ rationalSupportCohomology X L n :=
  biprod.lift (supportCohomologyEnlargement X Set.inter_subset_left n)
    (supportCohomologyEnlargement X Set.inter_subset_right n)

/-- The second support map is the difference of the two actual enlargements. -/
def supportCohomologyMayerVietorisSecond (X : TopCat.{0}) (K L : Set X) (n : ℕ) :
    rationalSupportCohomology X K n ⊞ rationalSupportCohomology X L n ⟶
      rationalSupportCohomology X (K ∪ L) n :=
  biprod.desc (supportCohomologyEnlargement X Set.subset_union_left n)
    (-supportCohomologyEnlargement X Set.subset_union_right n)

@[reassoc]
theorem supportCohomologyMayerVietorisFirst_comparison (X : TopCat.{0})
    (K L : Set X) (n : ℕ) :
    relativeRationalMayerVietorisFirst X Kᶜ Lᶜ n =
      (supportIntersectionCohomologyIso X K L n).hom ≫
        supportCohomologyMayerVietorisFirst X K L n := by
  apply biprod.hom_ext
  · simp only [Category.assoc, relativeRationalMayerVietorisFirst_fst,
      supportCohomologyMayerVietorisFirst, biprod.lift_fst]
    exact (relativeRationalSubsetCohomologyMap_source_congr X
      (Set.compl_inter K L).symm Set.subset_union_left
      (fun _ hx hxKL => hx hxKL.1) n).symm
  · simp only [Category.assoc, relativeRationalMayerVietorisFirst_snd,
      supportCohomologyMayerVietorisFirst, biprod.lift_snd]
    exact (relativeRationalSubsetCohomologyMap_source_congr X
      (Set.compl_inter K L).symm Set.subset_union_right
      (fun _ hx hxKL => hx hxKL.2) n).symm

@[reassoc]
theorem supportCohomologyMayerVietorisSecond_comparison (X : TopCat.{0})
    (K L : Set X) (n : ℕ) :
    relativeRationalMayerVietorisSecond X Kᶜ Lᶜ n ≫
        (supportUnionCohomologyIso X K L n).hom =
      supportCohomologyMayerVietorisSecond X K L n := by
  apply biprod.hom_ext'
  · simp only [relativeRationalMayerVietorisSecond_inl_assoc,
      supportCohomologyMayerVietorisSecond, biprod.inl_desc]
    exact relativeRationalSubsetCohomologyMap_target_congr X
      (Set.compl_union K L).symm Set.inter_subset_left
      (fun _ hx hxK => hx (Or.inl hxK)) n
  · simp only [relativeRationalMayerVietorisSecond_inr_assoc,
      supportCohomologyMayerVietorisSecond, biprod.inr_desc, Preadditive.neg_comp]
    exact congrArg Neg.neg (relativeRationalSubsetCohomologyMap_target_congr X
      (Set.compl_union K L).symm Set.inter_subset_right
      (fun _ hx hxL => hx (Or.inr hxL)) n)

/-- The genuine connecting morphism in cohomology with closed supports. -/
def supportCohomologyMayerVietorisBoundary (X : TopCat.{0}) (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L) (n : ℕ) :
    rationalSupportCohomology X (K ∪ L) n ⟶
      rationalSupportCohomology X (K ∩ L) (n + 1) :=
  (supportUnionCohomologyIso X K L n).inv ≫
    relativeRationalMayerVietorisBoundary X Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl n ≫
    (supportIntersectionCohomologyIso X K L (n + 1)).hom

/-- The support Mayer--Vietoris sequence with its standard (+,+), (+,-) convention. -/
def supportCohomologyMayerVietorisSequence (X : TopCat.{0}) (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L) (n : ℕ) :
    ComposableArrows (ModuleCat.{0} ℚ) 5 :=
  ComposableArrows.mk₅ (supportCohomologyMayerVietorisFirst X K L n)
    (supportCohomologyMayerVietorisSecond X K L n)
    (supportCohomologyMayerVietorisBoundary X K L hK hL n)
    (supportCohomologyMayerVietorisFirst X K L (n + 1))
    (supportCohomologyMayerVietorisSecond X K L (n + 1))

/-- The support sequence is exactly the relative sequence of the open complements. -/
def supportCohomologyMayerVietorisSequenceIso (X : TopCat.{0}) (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L) (n : ℕ) :
    relativeRationalMayerVietorisSequence X Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl n ≅
      supportCohomologyMayerVietorisSequence X K L hK hL n := by
  refine ComposableArrows.isoMk₅
    (supportIntersectionCohomologyIso X K L n) (Iso.refl _)
    (supportUnionCohomologyIso X K L n)
    (supportIntersectionCohomologyIso X K L (n + 1)) (Iso.refl _)
    (supportUnionCohomologyIso X K L (n + 1)) ?_ ?_ ?_ ?_ ?_
  · change relativeRationalMayerVietorisFirst X Kᶜ Lᶜ n ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact supportCohomologyMayerVietorisFirst_comparison X K L n
  · change relativeRationalMayerVietorisSecond X Kᶜ Lᶜ n ≫ _ = 𝟙 _ ≫ _
    rw [Category.id_comp]
    exact supportCohomologyMayerVietorisSecond_comparison X K L n
  · change relativeRationalMayerVietorisBoundary X Kᶜ Lᶜ
      hK.isOpen_compl hL.isOpen_compl n ≫
        (supportIntersectionCohomologyIso X K L (n + 1)).hom =
      (supportUnionCohomologyIso X K L n).hom ≫
        (supportUnionCohomologyIso X K L n).inv ≫
        relativeRationalMayerVietorisBoundary X Kᶜ Lᶜ
          hK.isOpen_compl hL.isOpen_compl n ≫
        (supportIntersectionCohomologyIso X K L (n + 1)).hom
    rw [Iso.hom_inv_id_assoc]
  · change relativeRationalMayerVietorisFirst X Kᶜ Lᶜ (n + 1) ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact supportCohomologyMayerVietorisFirst_comparison X K L (n + 1)
  · change relativeRationalMayerVietorisSecond X Kᶜ Lᶜ (n + 1) ≫ _ = 𝟙 _ ≫ _
    rw [Category.id_comp]
    exact supportCohomologyMayerVietorisSecond_comparison X K L (n + 1)

/-- Mayer--Vietoris for actual rational cohomology with arbitrary closed supports. -/
theorem supportCohomologyMayerVietorisSequence_exact (X : TopCat.{0}) (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L) (n : ℕ) :
    (supportCohomologyMayerVietorisSequence X K L hK hL n).Exact :=
  ComposableArrows.exact_of_iso (supportCohomologyMayerVietorisSequenceIso X K L hK hL n)
    (relativeRationalMayerVietorisSequence_exact X Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl n)

theorem supportCohomologyMayerVietoris_range_first (X : TopCat.{0}) (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L) (n : ℕ) :
    LinearMap.range (supportCohomologyMayerVietorisFirst X K L n).hom =
      LinearMap.ker (supportCohomologyMayerVietorisSecond X K L n).hom :=
  ((supportCohomologyMayerVietorisSequence_exact X K L hK hL n).exact 0).moduleCat_range_eq_ker

theorem supportCohomologyMayerVietoris_range_second (X : TopCat.{0}) (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L) (n : ℕ) :
    LinearMap.range (supportCohomologyMayerVietorisSecond X K L n).hom =
      LinearMap.ker (supportCohomologyMayerVietorisBoundary X K L hK hL n).hom :=
  ((supportCohomologyMayerVietorisSequence_exact X K L hK hL n).exact 1).moduleCat_range_eq_ker

theorem supportCohomologyMayerVietoris_range_boundary (X : TopCat.{0}) (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L) (n : ℕ) :
    LinearMap.range (supportCohomologyMayerVietorisBoundary X K L hK hL n).hom =
      LinearMap.ker (supportCohomologyMayerVietorisFirst X K L (n + 1)).hom :=
  ((supportCohomologyMayerVietorisSequence_exact X K L hK hL n).exact 2).moduleCat_range_eq_ker

/-- In a Hausdorff space compact supports satisfy the required closedness automatically. -/
theorem compactSupportStageMayerVietorisSequence_exact (X : TopCat.{0}) [T2Space X]
    (K L : TopologicalSpace.Compacts X) (n : ℕ) :
    (supportCohomologyMayerVietorisSequence X K L K.isCompact.isClosed L.isCompact.isClosed n).Exact :=
  supportCohomologyMayerVietorisSequence_exact X K L K.isCompact.isClosed L.isCompact.isClosed n

end

end OAI.AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris
