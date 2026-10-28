import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafRestriction

/-! # Tensor Restriction -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorRestriction.Construction

noncomputable section

/-! Tensor products commute with restriction to open subschemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

universe u

local instance (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

local instance {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e

local instance {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    RingHomInvPair e.symm.toRingHom e.toRingHom :=
  RingHomInvPair.of_ringEquiv e.symm

def restrictScalarsSemilinearEquiv {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (M : ModuleCat.{u} S) :
    (ModuleCat.restrictScalars e.toRingHom).obj M ≃ₛₗ[e.toRingHom] M where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restricting scalars along a ring isomorphism commutes with tensor products. -/
def restrictScalarsTensorIso {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (M N : ModuleCat.{u} S) :
    (ModuleCat.restrictScalars e.toRingHom).obj M ⊗
      (ModuleCat.restrictScalars e.toRingHom).obj N ≅
        (ModuleCat.restrictScalars e.toRingHom).obj (M ⊗ N) := by
  let t := TensorProduct.congr (restrictScalarsSemilinearEquiv e M)
    (restrictScalarsSemilinearEquiv e N)
  exact ModuleCat.isoMk t.toAddEquiv.toAddCommGrpIso (fun r ↦ by
    ext x
    exact (t.map_smulₛₗ r x).symm)

theorem restrictScalarsTensorIso_hom_tmul {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (M N : ModuleCat.{u} S) (m : M) (n : N) :
    (restrictScalarsTensorIso e M N).hom (m ⊗ₜ[R] n) = m ⊗ₜ[S] n := rfl

/-- Tensoring module presheaves commutes with open restriction. -/
def restrictPresheafTensorIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M N : Y.PresheafOfModules) :
    (SheafRestriction.Construction.restrictModulePresheaf f).obj M ⊗ (SheafRestriction.Construction.restrictModulePresheaf f).obj N ≅
      (SheafRestriction.Construction.restrictModulePresheaf f).obj (M ⊗ N) := by
  refine PresheafOfModules.isoMk (fun U ↦ ?_) ?_
  · exact restrictScalarsTensorIso
      (f.appIso U.unop).symm.commRingCatIsoToRingEquiv
      (M.obj (.op (f ''ᵁ U.unop))) (N.obj (.op (f ''ᵁ U.unop)))
  · intro U V h
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    rfl

/-- Tensoring module sheaves commutes with restriction to an open subscheme. -/
def restrictSheafTensorIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M N : Y.Modules) :
    SheafTensor.Construction.sheafTensor (M.restrict f) (N.restrict f) ≅ (SheafTensor.Construction.sheafTensor M N).restrict f :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (restrictPresheafTensorIso f M.val N.val) ≪≫
      SheafRestriction.Construction.restrictSheafificationIso f (M.val ⊗ N.val)

/-- The pullback description of the tensor-restriction isomorphism. -/
def pullbackSheafTensorIso_of_openImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules) :
    (Scheme.Modules.pullback f).obj (SheafTensor.Construction.sheafTensor M N) ≅
      SheafTensor.Construction.sheafTensor ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) :=
  ((Scheme.Modules.restrictFunctorIsoPullback f).app (SheafTensor.Construction.sheafTensor M N)).symm ≪≫
    (restrictSheafTensorIso f M N).symm ≪≫
    SheafTensor.Construction.sheafTensorCongr ((Scheme.Modules.restrictFunctorIsoPullback f).app M)
      ((Scheme.Modules.restrictFunctorIsoPullback f).app N)

/-- A trivialization remains a trivialization after shrinking its open domain. -/
def restrictLineBundleTrivialization {X : Scheme.{u}} {M : X.Modules}
    {U V : X.Opens} (hVU : V ≤ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ LineBundle.Construction.structureSheafModule U.toScheme) :
    (Scheme.Modules.pullback V.ι).obj M ≅ LineBundle.Construction.structureSheafModule V.toScheme :=
  (Scheme.Modules.pullbackCongr (X.homOfLE_ι hVU).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (X.homOfLE hVU) U.ι).app M).symm ≪≫
    (Scheme.Modules.pullback (X.homOfLE hVU)).mapIso e ≪≫
    LineBundle.Construction.pullbackStructureSheafIso (X.homOfLE hVU)

/-- The tensor product of two line bundles is a line bundle. -/
theorem isLineBundle_sheafTensor {X : Scheme.{u}} {M N : X.Modules}
    (hM : LineBundle.Construction.IsLineBundle M) (hN : LineBundle.Construction.IsLineBundle N) : LineBundle.Construction.IsLineBundle (SheafTensor.Construction.sheafTensor M N) := by
  intro x
  obtain ⟨U, hxU, ⟨eU⟩⟩ := hM x
  obtain ⟨V, hxV, ⟨eV⟩⟩ := hN x
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, ⟨?_⟩⟩
  exact pullbackSheafTensorIso_of_openImmersion (U ⊓ V).ι M N ≪≫
    SheafTensor.Construction.sheafTensorCongr (restrictLineBundleTrivialization inf_le_left eU)
      (restrictLineBundleTrivialization inf_le_right eV) ≪≫
    SheafTensor.Construction.sheafTensorUnitLeft (LineBundle.Construction.structureSheafModule (U ⊓ V).toScheme)

/-- Nonnegative tensor powers of a sheaf of modules. -/
def sheafTensorPower {X : Scheme.{u}} (M : X.Modules) : ℕ → X.Modules
  | 0 => LineBundle.Construction.structureSheafModule X
  | n + 1 => SheafTensor.Construction.sheafTensor (sheafTensorPower M n) M

theorem isLineBundle_sheafTensorPower {X : Scheme.{u}} {M : X.Modules}
    (hM : LineBundle.Construction.IsLineBundle M) (n : ℕ) : LineBundle.Construction.IsLineBundle (Construction.sheafTensorPower M n) := by
  induction n with
  | zero => exact LineBundle.Construction.isLineBundle_structureSheaf X
  | succ n ih => exact isLineBundle_sheafTensor ih hM

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorRestriction.Construction
