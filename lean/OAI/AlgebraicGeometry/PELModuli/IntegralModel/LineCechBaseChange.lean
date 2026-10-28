import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldLineLocalSections
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorCechComplex
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorCechTmul
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ShortComplexFirstCycles
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FlatBaseChangeKernel

/-! # Line Cech Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineCechBaseChange

noncomputable section

/-! Generic affine and line-bundle base change, isolated from the Openness
statement-dependent group-theoretic import chain. All constructions below
are proved here and retain the actual scheme-module section maps. -/

/-! Termwise coordinates for the actual line-bundle Cech complex after affine base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

namespace FieldBaseChange

universe u

variable {R : Type u} (K : Type u) [CommRing R] [CommRing K] [Algebra R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (M : X.Modules) (U : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleOn.Construction.LineBundleAffineCover M)

abbrev lineBundleBaseChangedCoefficients :=
  (FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf (pullback.snd f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))).obj
    ((Scheme.Modules.pullback (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K))).obj M)

abbrev lineBundleBaseChangedOpens : U.index → (pullback f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K)).Opens :=
  fun i ↦ (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K)) ⁻¹ᵁ U.opens i

theorem lineBundleBaseChangedOpens_cover : iSup (lineBundleBaseChangedOpens K f M U) = ⊤ := by
  change (⨆ i, (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K)) ⁻¹ᵁ U.opens i) = ⊤
  rw [← Scheme.Hom.preimage_iSup, U.cover]
  rfl

def lineBundleCechBaseChangeCoordinates0 :
    ArithmeticGeometry.OrdinaryLocus.Openness.CechBaseChangeCoordinates.Construction.tensorCechC0 (K := K) ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M) U.opens ≃ₗ[K]
      ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechDegreeZero.Construction.openModuleCechC0 (lineBundleBaseChangedCoefficients K f M) (lineBundleBaseChangedOpens K f M U) :=
  LinearEquiv.piCongrRight fun i ↦
    FieldLineLocalSections.FieldBaseChange.affineBaseChangeLineBundlePreimageEquiv K f M (U.opens i) (U.affine i) (U.trivialization i)

variable [IsSeparated f]

def lineBundleCechBaseChangeCoordinates1 :
    ArithmeticGeometry.OrdinaryLocus.Openness.CechBaseChangeCoordinates.Construction.tensorCechC1 (K := K) ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M) U.opens ≃ₗ[K]
      ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechDegreeZero.Construction.openModuleCechC1 (lineBundleBaseChangedCoefficients K f M) (lineBundleBaseChangedOpens K f M U) :=
  LinearEquiv.piCongrRight fun i ↦ LinearEquiv.piCongrRight fun j ↦
    FieldLineLocalSections.FieldBaseChange.affineBaseChangeLineBundlePreimageEquiv K f M (U.opens i ⊓ U.opens j)
      (FieldLineLocalSections.FieldBaseChange.affine_inter_of_separated_base f _ _ (U.affine i) (U.affine j))
      (U.trivializationOn i _ inf_le_left)

def lineBundleCechBaseChangeCoordinates2 :
    ArithmeticGeometry.OrdinaryLocus.Openness.CechBaseChangeCoordinates.Construction.tensorCechC2 (K := K) ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M) U.opens ≃ₗ[K]
      ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechShortComplex.Construction.openModuleCechC2 (lineBundleBaseChangedCoefficients K f M) (lineBundleBaseChangedOpens K f M U) :=
  LinearEquiv.piCongrRight fun i ↦ LinearEquiv.piCongrRight fun j ↦ LinearEquiv.piCongrRight fun k ↦
    FieldLineLocalSections.FieldBaseChange.affineBaseChangeLineBundlePreimageEquiv K f M ((U.opens i ⊓ U.opens j) ⊓ U.opens k)
      (FieldLineLocalSections.FieldBaseChange.affine_inter_of_separated_base f _ _
        (FieldLineLocalSections.FieldBaseChange.affine_inter_of_separated_base f _ _ (U.affine i) (U.affine j)) (U.affine k))
      (U.trivializationOn i _ (inf_le_left.trans inf_le_left))

end FieldBaseChange

/-! The actual line-bundle Cech complex commutes with arbitrary affine base change. -/

namespace FieldBaseChange

universe u

variable {R : Type u} (K : Type u) [CommRing R] [CommRing K] [Algebra R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (M : X.Modules)

def lineBundleAffineTrivialOpen (W : X.Opens) : Prop :=
  IsAffineOpen W ∧ Nonempty ((Scheme.Modules.pullback W.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule W.toScheme)

def lineBundleTensorCechLocalComparison :
    ArithmeticGeometry.OrdinaryLocus.Openness.TensorCechTmul.Construction.TensorCechLocalComparison (pullback.fst f (FieldAffineSections.FieldBaseChange.affineBaseChangeMap R K)).base
      ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M) (lineBundleBaseChangedCoefficients K f M)
      (lineBundleAffineTrivialOpen M) where
  sectionEquiv W hW := FieldLineLocalSections.FieldBaseChange.affineBaseChangeLineBundlePreimageEquiv K f M W hW.1 hW.2.some
  restrict i hU hV z :=
    FieldLineLocalSections.FieldBaseChange.affineBaseChangeLineBundlePreimageEquiv_restrict K f M i hU.1 hV.1 hU.2.some hV.2.some z

variable [IsSeparated f] (U : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleOn.Construction.LineBundleAffineCover M)

def lineBundleCechBaseChangeIso :
    ArithmeticGeometry.OrdinaryLocus.Openness.ModuleBaseChangeComplex.Construction.moduleBaseChangeComplex R K (FieldSectionModules.FieldBaseChange.schemeModuleCechShortComplex f M U.opens) ≅
      ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechShortComplex.Construction.openModuleCechShortComplex (lineBundleBaseChangedCoefficients K f M)
        (lineBundleBaseChangedOpens K f M U) := by
  classical
  exact (lineBundleTensorCechLocalComparison K f M).complexIso U.opens
    (fun i ↦ ⟨U.affine i, ⟨U.trivialization i⟩⟩)
    (fun i j ↦ ⟨FieldLineLocalSections.FieldBaseChange.affine_inter_of_separated_base f _ _ (U.affine i) (U.affine j),
      ⟨U.trivializationOn i _ inf_le_left⟩⟩)
    (fun i j k ↦ ⟨FieldLineLocalSections.FieldBaseChange.affine_inter_of_separated_base f _ _
      (FieldLineLocalSections.FieldBaseChange.affine_inter_of_separated_base f _ _ (U.affine i) (U.affine j)) (U.affine k),
      ⟨U.trivializationOn i _ (inf_le_left.trans inf_le_left)⟩⟩)

def lineBundleCechBaseChangeHomologyIso :
    (ArithmeticGeometry.OrdinaryLocus.Openness.ModuleBaseChangeComplex.Construction.moduleBaseChangeComplex R K (FieldSectionModules.FieldBaseChange.schemeModuleCechShortComplex f M U.opens)).homology ≅
      ModuleCat.of K (ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechCohomology.Construction.OpenCechH1 (lineBundleBaseChangedCoefficients K f M)
        (lineBundleBaseChangedOpens K f M U)) :=
  ShortComplex.homologyMapIso (lineBundleCechBaseChangeIso K f M U) ≪≫
    ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechHomologyIso.Construction.openModuleCechHomologyIso (lineBundleBaseChangedCoefficients K f M)
      (lineBundleBaseChangedOpens K f M U)

end FieldBaseChange

/-! The first cycles of the tensor Cech complex are actual global sections after base change. -/

namespace FieldBaseChange

universe u v

def shortComplexFirstCyclesEquivOfIso {R : Type u} [CommRing R]
    {S T : ShortComplex (ModuleCat.{v} R)} (e : S ≅ T) :
    LinearMap.ker S.f.hom ≃ₗ[R] LinearMap.ker T.f.hom :=
  LinearEquiv.ofLinearMap (ArithmeticGeometry.OrdinaryLocus.Openness.ShortComplexFirstCycles.Construction.shortComplexFirstCyclesMap e.hom) (ArithmeticGeometry.OrdinaryLocus.Openness.ShortComplexFirstCycles.Construction.shortComplexFirstCyclesMap e.inv)
    (by rw [← ArithmeticGeometry.OrdinaryLocus.Openness.ShortComplexFirstCycles.Construction.shortComplexFirstCyclesMap_comp, e.inv_hom_id, ArithmeticGeometry.OrdinaryLocus.Openness.ShortComplexFirstCycles.Construction.shortComplexFirstCyclesMap_id])
    (by rw [← ArithmeticGeometry.OrdinaryLocus.Openness.ShortComplexFirstCycles.Construction.shortComplexFirstCyclesMap_comp, e.hom_inv_id, ArithmeticGeometry.OrdinaryLocus.Openness.ShortComplexFirstCycles.Construction.shortComplexFirstCyclesMap_id])

def moduleBaseChangeFirstCycle {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (S : ShortComplex (ModuleCat.{u} R)) (a : K) (x : LinearMap.ker S.f.hom) :
    LinearMap.ker (ArithmeticGeometry.OrdinaryLocus.Openness.ModuleBaseChangeComplex.Construction.moduleBaseChangeComplex R K S).f.hom :=
  ⟨a ⊗ₜ[R] x.val, by
    change a ⊗ₜ[R] S.f x.val = 0
    rw [show S.f x.val = 0 from x.property, TensorProduct.tmul_zero]⟩

variable {R : Type u} (K : Type u) [CommRing R] [CommRing K] [Algebra R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsSeparated f]
    (M : X.Modules) (U : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleOn.Construction.LineBundleAffineCover M)

theorem lineBundleCechBaseChangeIso_first_tmul (a : K)
    (z : ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechDegreeZero.Construction.openModuleCechC0 ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M) U.opens) (i : U.index) :
    (lineBundleCechBaseChangeIso K f M U).hom.τ₁ (a ⊗ₜ[R] z) i =
      a • FieldLineLocalSections.FieldBaseChange.affineBaseChangePreimageSection K f M (U.opens i) (z i) := by
  classical
  have h₀ (i : U.index) : lineBundleAffineTrivialOpen M (U.opens i) :=
    ⟨U.affine i, ⟨U.trivialization i⟩⟩
  have h₁ (i j : U.index) : lineBundleAffineTrivialOpen M (U.opens i ⊓ U.opens j) :=
    ⟨FieldLineLocalSections.FieldBaseChange.affine_inter_of_separated_base f _ _ (U.affine i) (U.affine j),
      ⟨U.trivializationOn i _ inf_le_left⟩⟩
  have h₂ (i j k : U.index) : lineBundleAffineTrivialOpen M ((U.opens i ⊓ U.opens j) ⊓ U.opens k) :=
    ⟨FieldLineLocalSections.FieldBaseChange.affine_inter_of_separated_base f _ _
      (FieldLineLocalSections.FieldBaseChange.affine_inter_of_separated_base f _ _ (U.affine i) (U.affine j)) (U.affine k),
      ⟨U.trivializationOn i _ (inf_le_left.trans inf_le_left)⟩⟩
  exact ((lineBundleTensorCechLocalComparison K f M).complexIso_first_tmul
    U.opens h₀ h₁ h₂ a z i).trans
      (FieldLineLocalSections.FieldBaseChange.affineBaseChangeLineBundlePreimageEquiv_tmul K f M (U.opens i) (h₀ i).1 (h₀ i).2.some a (z i))

def lineBundleCechBaseChangeSectionsEquiv :
    LinearMap.ker (ArithmeticGeometry.OrdinaryLocus.Openness.ModuleBaseChangeComplex.Construction.moduleBaseChangeComplex R K (FieldSectionModules.FieldBaseChange.schemeModuleCechShortComplex f M U.opens)).f.hom ≃ₗ[K]
      (lineBundleBaseChangedCoefficients K f M).obj.obj (op ⊤) :=
  (shortComplexFirstCyclesEquivOfIso (lineBundleCechBaseChangeIso K f M U)).trans
    (ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechHomologyIso.Construction.openModuleCechGlobalSectionsEquiv (lineBundleBaseChangedCoefficients K f M)
      (lineBundleBaseChangedOpens K f M U) (lineBundleBaseChangedOpens_cover K f M U)).symm

theorem lineBundleCechBaseChangeSectionsEquiv_tmul (a : K)
    (m : ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.obj (op ⊤)) :
    lineBundleCechBaseChangeSectionsEquiv K f M U
      (moduleBaseChangeFirstCycle (FieldSectionModules.FieldBaseChange.schemeModuleCechShortComplex f M U.opens) a
        (ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechHomologyIso.Construction.openModuleCechGlobalSectionsEquiv ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M) U.opens U.cover m)) =
      a • FieldLineLocalSections.FieldBaseChange.affineBaseChangePreimageSection K f M ⊤ m := by
  let G := lineBundleBaseChangedCoefficients K f M
  let V := lineBundleBaseChangedOpens K f M U
  let g := ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechHomologyIso.Construction.openModuleCechGlobalSectionsEquiv G V (lineBundleBaseChangedOpens_cover K f M U)
  let x := moduleBaseChangeFirstCycle (FieldSectionModules.FieldBaseChange.schemeModuleCechShortComplex f M U.opens) a
    (ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechHomologyIso.Construction.openModuleCechGlobalSectionsEquiv ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M) U.opens U.cover m)
  apply g.injective
  change g (g.symm ((shortComplexFirstCyclesEquivOfIso (lineBundleCechBaseChangeIso K f M U)) x)) = _
  rw [g.apply_symm_apply]
  apply Subtype.ext
  funext i
  have h := lineBundleCechBaseChangeIso_first_tmul K f M U a
    (ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechDegreeZero.Construction.openModuleCechUnit ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M) U.opens m) i
  have hr := FieldLineLocalSections.FieldBaseChange.affineBaseChangePreimageSection_restrict K f M
    (homOfLE le_top : U.opens i ⟶ ⊤) m
  have hs := (G.obj.map (homOfLE le_top : V i ⟶ ⊤).op).hom.map_smul a
    (FieldLineLocalSections.FieldBaseChange.affineBaseChangePreimageSection K f M ⊤ m)
  exact h.trans ((congrArg (fun z : G.obj.obj (op (V i)) ↦ a • z) hr).trans hs.symm)

end FieldBaseChange

/-! Flat affine base change commutes with the actual global sections of a line bundle. -/

namespace FieldBaseChange

universe u

variable {R : Type u} (K : Type u) [CommRing R] [CommRing K] [Algebra R K] [Module.Flat R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsSeparated f]
    (M : X.Modules) (U : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleOn.Construction.LineBundleAffineCover M)

def flatLineBundleGlobalSectionsEquiv :
    (K ⊗[R] (((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.obj (op ⊤))) ≃ₗ[K]
      (lineBundleBaseChangedCoefficients K f M).obj.obj (op ⊤) :=
  ((ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechHomologyIso.Construction.openModuleCechGlobalSectionsEquiv ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M) U.opens U.cover).baseChange
    R K _ _).trans
      ((ArithmeticGeometry.OrdinaryLocus.Openness.FlatBaseChangeKernel.Construction.flatBaseChangeKernelEquiv K (FieldSectionModules.FieldBaseChange.schemeModuleCechShortComplex f M U.opens).f.hom).trans
        (lineBundleCechBaseChangeSectionsEquiv K f M U))

theorem flatLineBundleGlobalSectionsEquiv_tmul (a : K)
    (m : ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.obj (op ⊤)) :
    flatLineBundleGlobalSectionsEquiv K f M U (a ⊗ₜ[R] m) =
      a • FieldLineLocalSections.FieldBaseChange.affineBaseChangePreimageSection K f M ⊤ m := by
  let S := FieldSectionModules.FieldBaseChange.schemeModuleCechShortComplex f M U.opens
  let g := ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechHomologyIso.Construction.openModuleCechGlobalSectionsEquiv ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M) U.opens U.cover
  have hx : ArithmeticGeometry.OrdinaryLocus.Openness.FlatBaseChangeKernel.Construction.flatBaseChangeKernelEquiv K S.f.hom (a ⊗ₜ[R] g m) =
      moduleBaseChangeFirstCycle S a (g m) := by
    apply Subtype.ext
    rfl
  have hg : g.baseChange R K _ _ (a ⊗ₜ[R] m) = a ⊗ₜ[R] g m :=
    LinearEquiv.baseChange_tmul R K _ _ a m
  exact (congrArg (fun z ↦ lineBundleCechBaseChangeSectionsEquiv K f M U
    (ArithmeticGeometry.OrdinaryLocus.Openness.FlatBaseChangeKernel.Construction.flatBaseChangeKernelEquiv K S.f.hom z)) hg).trans
      ((congrArg (lineBundleCechBaseChangeSectionsEquiv K f M U) hx).trans
        (lineBundleCechBaseChangeSectionsEquiv_tmul K f M U a m))

def lineBundleChosenAffineCover [QuasiCompact f] (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleOn.Construction.LineBundleAffineCover M := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleOn.Construction.exists_lineBundleAffineCover M hM).some

def lineBundleFlatBaseChangeGlobalSectionsEquiv [QuasiCompact f] (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) :
    (K ⊗[R] (((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.obj (op ⊤))) ≃ₗ[K]
      (lineBundleBaseChangedCoefficients K f M).obj.obj (op ⊤) :=
  flatLineBundleGlobalSectionsEquiv K f M (lineBundleChosenAffineCover f M hM)

theorem lineBundleFlatBaseChangeGlobalSectionsEquiv_tmul [QuasiCompact f] (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M)
    (a : K) (m : ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.obj (op ⊤)) :
    lineBundleFlatBaseChangeGlobalSectionsEquiv K f M hM (a ⊗ₜ[R] m) =
      a • FieldLineLocalSections.FieldBaseChange.affineBaseChangePreimageSection K f M ⊤ m :=
  flatLineBundleGlobalSectionsEquiv_tmul K f M (lineBundleChosenAffineCover f M hM) a m

end FieldBaseChange

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineCechBaseChange
