import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.CechPotentialMem
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CechDifferential

/-! # Cech Potential Add -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.CechPotentialAdd.HolomorphicCechPrimitive

noncomputable section

section

/-! The actual cocycle-extension equation provides a glued native
holomorphic potential for every section of the extension module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {I : Type} {U : I → V.carrier.Opens}
    {z : Γ(Cech.TermModules.cechTermModule V.carrier U 1, ⊤)} (D : CechPotentialMem.HolomorphicCechPrimitive V U z)
    (hU : iSup U = ⊤) (hz : (Cech.ModuleDifferential.cechModuleDifferential V.carrier U 1).app ⊤ z = 0)

local notation "S" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ExtensionCoordinates.cechCocycleExtension V.carrier U (OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ExtensionCoordinates.cechOneCycleHom V.carrier U z hz)
local notation "A" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ExtensionCoordinates.cechCocycleZeroProjection V.carrier U (OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ExtensionCoordinates.cechOneCycleHom V.carrier U z hz)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.CechPotentialMem.HolomorphicCechPrimitive.extensionPotential (W : V.carrier.Opens) (m : Γ((S).X₂, W)) :
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel) (M := DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W) :=
  D.potential hU W ((A).app W m) ((S).g.app W m) (Cech.ExtensionCoordinates.cechOneCycle_local_equation V.carrier U z hz W m)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.CechPotentialMem.HolomorphicCechPrimitive.extensionPotential_value (W : V.carrier.Opens) (m : Γ((S).X₂, W)) (i : I) (x : V.analyticSpace)
    (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex i)) :
    D.extensionPotential hU hz W m ⟨x, hx.1⟩ =
      Intrinsic.CechDifferential.nativeCechValue V U 0 W ((A).app W m) (Cech.PairCoordinates.cechSingletonIndex i) x hx -
        RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left W hx.1 ((S).g.app W m) * D.coefficient i ⟨x, hx.2⟩ :=
  D.potential_value hU W ((A).app W m) ((S).g.app W m) (Cech.ExtensionCoordinates.cechOneCycle_local_equation V.carrier U z hz W m) i x hx

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.CechPotentialMem.HolomorphicCechPrimitive.extensionPotential_add (W : V.carrier.Opens) (m n : Γ((S).X₂, W)) :
    D.extensionPotential hU hz W (m + n) = D.extensionPotential hU hz W m + D.extensionPotential hU hz W n := by
  apply DFunLike.ext
  intro x
  obtain ⟨i, hi⟩ := CechPotentialMem.cechSingleton_cover U hU (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val)
  have hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ W ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex i) := ⟨x.property, hi⟩
  change D.extensionPotential hU hz W (m + n) x =
    D.extensionPotential hU hz W m x + D.extensionPotential hU hz W n x
  rw [D.extensionPotential_value hU hz W (m + n) i x.val hx,
    D.extensionPotential_value hU hz W m i x.val hx, D.extensionPotential_value hU hz W n i x.val hx]
  have hA : (A).app W (m + n) = (A).app W m + (A).app W n :=
    (HilbertConstruction.Tensor.Powers.SheafMultilinearMap.homApp A W).map_add m n
  have hR : (S).g.app W (m + n) = (S).g.app W m + (S).g.app W n :=
    (HilbertConstruction.Tensor.Powers.SheafMultilinearMap.homApp (S).g W).map_add m n
  erw [hA, hR, Intrinsic.CechDifferential.nativeCechValue_add, map_add]
  ring

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.CechPotentialMem.HolomorphicCechPrimitive.extensionPotential_smul (W : V.carrier.Opens) (a : Γ(V.carrier, W)) (m : Γ((S).X₂, W)) :
    D.extensionPotential hU hz W (a • m) =
      DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V W a * D.extensionPotential hU hz W m := by
  apply DFunLike.ext
  intro x
  obtain ⟨i, hi⟩ := CechPotentialMem.cechSingleton_cover U hU (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val)
  have hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ W ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex i) := ⟨x.property, hi⟩
  change D.extensionPotential hU hz W (a • m) x =
    DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V W a x * D.extensionPotential hU hz W m x
  rw [D.extensionPotential_value hU hz W (a • m) i x.val hx,
    D.extensionPotential_value hU hz W m i x.val hx]
  have hA : (A).app W (a • m) = a • (A).app W m :=
    (HilbertConstruction.Tensor.Powers.SheafMultilinearMap.homApp A W).map_smul a m
  have hR : (S).g.app W (a • m) = a • (S).g.app W m :=
    (HilbertConstruction.Tensor.Powers.SheafMultilinearMap.homApp (S).g W).map_smul a m
  have hRv := congrArg (RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.val.left W x.property) hR
  change RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.val.left W x.property ((S).g.app W (a • m)) =
    RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.val.left W x.property
      (a * (show Γ(V.carrier, W) from (S).g.app W m)) at hRv
  erw [map_mul] at hRv
  erw [hA, hRv, Intrinsic.CechDifferential.nativeCechValue_smul]
  have ha := Intrinsic.FrameEvaluation.sectionEvaluationOn_native V.presentation W a x
  change DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V W a x = RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.val.left W x.property a at ha
  rw [ha]
  ring

end

section

/-! Glued extension potentials commute with actual algebraic restriction
and normalize to native regular evaluation on the structure submodule. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {I : Type} {U : I → V.carrier.Opens}
    {z : Γ(Cech.TermModules.cechTermModule V.carrier U 1, ⊤)} (D : CechPotentialMem.HolomorphicCechPrimitive V U z)
    (hU : iSup U = ⊤) (hz : (Cech.ModuleDifferential.cechModuleDifferential V.carrier U 1).app ⊤ z = 0)

local notation "S" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ExtensionCoordinates.cechCocycleExtension V.carrier U (OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ExtensionCoordinates.cechOneCycleHom V.carrier U z hz)
local notation "A" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ExtensionCoordinates.cechCocycleZeroProjection V.carrier U (OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ExtensionCoordinates.cechOneCycleHom V.carrier U z hz)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.CechPotentialMem.HolomorphicCechPrimitive.extensionPotential_restrict {W Z : V.carrier.Opens} (h : Z ≤ W) (m : Γ((S).X₂, W)) :
    D.extensionPotential hU hz Z ((S).X₂.presheaf.map (homOfLE h).op m) =
      DivisorClass.Chern.HolomorphicSection.Data.holomorphicOpenRestriction (show DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation Z ≤
        DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W from fun _ hx => h hx)
          (D.extensionPotential hU hz W m) := by
  apply DFunLike.ext
  intro x
  obtain ⟨i, hi⟩ := CechPotentialMem.cechSingleton_cover U hU (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val)
  have hxZ : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ Z ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex i) := ⟨x.property, hi⟩
  have hxW : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ W ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex i) := ⟨h x.property, hi⟩
  change D.extensionPotential hU hz Z ((S).X₂.presheaf.map (homOfLE h).op m) x =
    D.extensionPotential hU hz W m ⟨x.val, h x.property⟩
  rw [D.extensionPotential_value hU hz Z _ i x.val hxZ, D.extensionPotential_value hU hz W m i x.val hxW]
  have hA := ConcreteCategory.congr_hom ((A).mapPresheaf.naturality (homOfLE h).op) m
  have hR := ConcreteCategory.congr_hom ((S).g.mapPresheaf.naturality (homOfLE h).op) m
  change (A).app Z ((S).X₂.presheaf.map (homOfLE h).op m) =
    (Cech.TermModules.cechTermModule V.carrier U 0).presheaf.map (homOfLE h).op ((A).app W m) at hA
  change (S).g.app Z ((S).X₂.presheaf.map (homOfLE h).op m) =
    V.carrier.presheaf.map (homOfLE h).op ((S).g.app W m) at hR
  erw [hA, hR, Intrinsic.CechDifferential.nativeCechValue_restrict, RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue_restrict]

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.CechPotentialMem.HolomorphicCechPrimitive.extensionPotential_inclusion (W : V.carrier.Opens) (a : Γ(V.carrier, W)) :
    D.extensionPotential hU hz W ((S).f.app W a) = DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V W a := by
  apply DFunLike.ext
  intro x
  obtain ⟨i, hi⟩ := CechPotentialMem.cechSingleton_cover U hU (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val)
  have hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ W ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex i) := ⟨x.property, hi⟩
  rw [D.extensionPotential_value hU hz W _ i x.val hx]
  have hA := congrArg (fun f => f.app W a)
    (Cech.ExtensionCoordinates.cechCocycleZeroProjection_inclusion V.carrier U (Cech.ExtensionCoordinates.cechOneCycleHom V.carrier U z hz))
  have hR := congrArg (fun f => f.app W a) (S).zero
  change (A).app W ((S).f.app W a) = (Cech.ModuleAugmentation.cechModuleAugmentation V.carrier U).app W a at hA
  change (S).g.app W ((S).f.app W a) = (0 : Γ(V.carrier, W)) at hR
  erw [hA, hR, Intrinsic.CechDifferential.nativeCechValue_augmentation, map_zero, zero_mul, sub_zero]
  exact (Intrinsic.FrameEvaluation.sectionEvaluationOn_native V.presentation W a x).symm

end

/-! A literal native holomorphic primitive of an algebraic Cech cocycle
produces an actual holomorphic sheaf retraction and hence an actual
algebraic Cech coboundary. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {I : Type} {U : I → V.carrier.Opens}
    {z : Γ(Cech.TermModules.cechTermModule V.carrier U 1, ⊤)} (D : CechPotentialMem.HolomorphicCechPrimitive V U z)
    (hU : iSup U = ⊤) (hz : (Cech.ModuleDifferential.cechModuleDifferential V.carrier U 1).app ⊤ z = 0)

local notation "S" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ExtensionCoordinates.cechCocycleExtension V.carrier U (OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ExtensionCoordinates.cechOneCycleHom V.carrier U z hz)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.CechPotentialMem.HolomorphicCechPrimitive.extensionFunctional : FunctionalNe.HolomorphicScalarFunctional V (S).X₂ := by
  let N := (DivisorClass.Chern.Holomorphic.ModuleAnalytification.holomorphicModuleDirectImage V).obj
    (SheafOfModules.unit (DivisorClass.Chern.HolomorphicSection.Modules.holomorphicStructureRingSheaf V.analyticModel V.analyticSpace))
  let f : (SheafOfModules.toSheaf V.carrier.ringCatSheaf).obj (S).X₂ ⟶
      (SheafOfModules.toSheaf V.carrier.ringCatSheaf).obj N := {
    hom := {
      app W := AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (D.extensionPotential hU hz W.unop) (D.extensionPotential_add hU hz W.unop))
      naturality := by
        intro W Z h
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro m
        exact D.extensionPotential_restrict hU hz (leOfHom h.unop) m } }
  exact ModuleHomOf.moduleHomOfAbelian f (fun W a m => D.extensionPotential_smul hU hz W a m)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.CechPotentialMem.HolomorphicCechPrimitive.extensionFunctional_normalization :
    (S).f ≫ D.extensionFunctional hU hz = FunctionalDescent.nativeStructureEvaluation V := by
  apply Scheme.Modules.hom_ext
  intro W
  ext a
  change D.extensionPotential hU hz W ((S).f.app W a) = DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V W a
  exact D.extensionPotential_inclusion hU hz W a

include D hU hz in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.CechPotentialMem.HolomorphicCechPrimitive.exists_algebraic_boundary :
    ∃ b : Γ(Cech.TermModules.cechTermModule V.carrier U 0, ⊤), (Cech.ModuleDifferential.cechModuleDifferential V.carrier U 0).app ⊤ b = z :=
  Cech.ExtensionCoordinates.cechOneCycle_boundary_of_holomorphicScalarRetraction V U hU z hz
    (D.extensionFunctional hU hz) (D.extensionFunctional_normalization hU hz)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.CechPotentialAdd.HolomorphicCechPrimitive
