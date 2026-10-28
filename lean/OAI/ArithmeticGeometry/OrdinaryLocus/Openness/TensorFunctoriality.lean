import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafRestriction

/-! # Tensor Functoriality -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorFunctoriality.Construction

noncomputable section

/-! Tensor maps for sheaves, pushforward, and pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

universe u

local instance tensorFunctorialityMonoidal (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

def sheafTensorMap {X : Scheme.{u}} {M M' N N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') : SheafTensor.Construction.sheafTensor M N ⟶ SheafTensor.Construction.sheafTensor M' N' :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (f.val ⊗ₘ g.val)

theorem sheafTensorMap_id {X : Scheme.{u}} (M N : X.Modules) :
    sheafTensorMap (𝟙 M) (𝟙 N) = 𝟙 (SheafTensor.Construction.sheafTensor M N) := by
  let F : X.PresheafOfModules ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  change F.map ((𝟙 M.val) ⊗ₘ (𝟙 N.val)) = 𝟙 (F.obj (M.val ⊗ N.val))
  exact (congrArg F.map (id_tensorHom_id M.val N.val)).trans (F.map_id _)

theorem sheafTensorMap_comp {X : Scheme.{u}} {M M' M'' N N' N'' : X.Modules}
    (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N'') :
    sheafTensorMap (f ≫ f') (g ≫ g') = sheafTensorMap f g ≫ sheafTensorMap f' g' := by
  let F : X.PresheafOfModules ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  change F.map ((f.val ≫ f'.val) ⊗ₘ (g.val ≫ g'.val)) =
    F.map (f.val ⊗ₘ g.val) ≫ F.map (f'.val ⊗ₘ g'.val)
  exact (congrArg F.map (tensorHom_comp_tensorHom f.val g.val f'.val g'.val).symm).trans
    (F.map_comp _ _)

theorem sheafTensorHomEquiv_naturality_left {X : Scheme.{u}}
    {M M' N N' P : X.Modules} (f : M ⟶ M') (g : N ⟶ N')
    (h : SheafTensor.Construction.sheafTensor M' N' ⟶ P) :
    SheafTensor.Construction.sheafTensorHomEquiv M N P (sheafTensorMap f g ≫ h) =
      (f.val ⊗ₘ g.val) ≫ SheafTensor.Construction.sheafTensorHomEquiv M' N' P h :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_naturality_left
    (f.val ⊗ₘ g.val) h

theorem sheafTensorHomEquiv_naturality_right {X : Scheme.{u}}
    {M N P Q : X.Modules} (h : SheafTensor.Construction.sheafTensor M N ⟶ P) (f : P ⟶ Q) :
    SheafTensor.Construction.sheafTensorHomEquiv M N Q (h ≫ f) = SheafTensor.Construction.sheafTensorHomEquiv M N P h ≫ f.val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_naturality_right h f

theorem moduleSheafificationUnit_naturality {X : Scheme.{u}}
    {M N : X.PresheafOfModules} (f : M ⟶ N) :
    f ≫ SheafRestriction.Construction.moduleSheafificationUnit N = SheafRestriction.Construction.moduleSheafificationUnit M ≫
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality f

def restrictScalarsSemilinearMap {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : ModuleCat.{u} S) :
    (ModuleCat.restrictScalars φ).obj M →ₛₗ[φ] M where
  toFun := id
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The tensor comparison for restriction of scalars along any ring map. -/
def restrictScalarsTensorMap {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (M N : ModuleCat.{u} S) :
    (ModuleCat.restrictScalars φ).obj M ⊗ (ModuleCat.restrictScalars φ).obj N ⟶
      (ModuleCat.restrictScalars φ).obj (M ⊗ N) :=
  let t := TensorProduct.map (restrictScalarsSemilinearMap φ M) (restrictScalarsSemilinearMap φ N)
  ModuleCat.ofHom (R := R)
    (X := ((ModuleCat.restrictScalars φ).obj M ⊗
      (ModuleCat.restrictScalars φ).obj N : ModuleCat R))
    (Y := ((ModuleCat.restrictScalars φ).obj (M ⊗ N) : ModuleCat R))
    { toFun := t
      map_add' := t.map_add
      map_smul' r x := t.map_smulₛₗ r x }

theorem restrictScalarsTensorMap_tmul {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (M N : ModuleCat.{u} S) (m : M) (n : N) :
    restrictScalarsTensorMap φ M N (m ⊗ₜ[R] n) = m ⊗ₜ[S] n := rfl

def pushforwardModulePresheaf {X Y : Scheme.{u}} (f : X ⟶ Y) :
    X.PresheafOfModules ⥤ Y.PresheafOfModules :=
  PresheafOfModules.pushforward f.toRingCatSheafHom.hom

def pushforwardPresheafTensorMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : X.PresheafOfModules) :
    (pushforwardModulePresheaf f).obj M ⊗ (pushforwardModulePresheaf f).obj N ⟶
      (pushforwardModulePresheaf f).obj (M ⊗ N) where
  app U := restrictScalarsTensorMap (f.app U.unop).hom
    (M.obj (.op (f ⁻¹ᵁ U.unop))) (N.obj (.op (f ⁻¹ᵁ U.unop)))
  naturality {U V} h := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    rfl

theorem pushforwardPresheafTensorMap_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M M' N N' : X.PresheafOfModules} (a : M ⟶ M') (b : N ⟶ N') :
    pushforwardPresheafTensorMap f M N ≫ (pushforwardModulePresheaf f).map (a ⊗ₘ b) =
      ((pushforwardModulePresheaf f).map a ⊗ₘ (pushforwardModulePresheaf f).map b) ≫
        pushforwardPresheafTensorMap f M' N' := by
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  rfl

/-- Tensoring two pushforwards maps naturally to the pushforward of their tensor product. -/
def pushforwardSheafTensorMap {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : X.Modules) :
    SheafTensor.Construction.sheafTensor ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N) ⟶
      (Scheme.Modules.pushforward f).obj (SheafTensor.Construction.sheafTensor M N) :=
  (SheafTensor.Construction.sheafTensorHomEquiv _ _ _).symm
    (pushforwardPresheafTensorMap f M.val N.val ≫
      (pushforwardModulePresheaf f).map
        (SheafRestriction.Construction.moduleSheafificationUnit (M.val ⊗ N.val)))

theorem pushforwardSheafTensorMap_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M M' N N' : X.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    pushforwardSheafTensorMap f M N ≫ (Scheme.Modules.pushforward f).map (sheafTensorMap a b) =
      sheafTensorMap ((Scheme.Modules.pushforward f).map a) ((Scheme.Modules.pushforward f).map b) ≫
        pushforwardSheafTensorMap f M' N' := by
  apply (SheafTensor.Construction.sheafTensorHomEquiv _ _ _).injective
  rw [sheafTensorHomEquiv_naturality_right, sheafTensorHomEquiv_naturality_left]
  simp only [pushforwardSheafTensorMap, Equiv.apply_symm_apply]
  let F := pushforwardModulePresheaf f
  let η₁ := SheafRestriction.Construction.moduleSheafificationUnit (M.val ⊗ N.val)
  let η₂ := SheafRestriction.Construction.moduleSheafificationUnit (M'.val ⊗ N'.val)
  let θ := (sheafTensorMap a b).val
  let q₁ := pushforwardPresheafTensorMap f M.val N.val
  let q₂ := pushforwardPresheafTensorMap f M'.val N'.val
  have hη : η₁ ≫ θ = (a.val ⊗ₘ b.val) ≫ η₂ :=
    (moduleSheafificationUnit_naturality (a.val ⊗ₘ b.val)).symm
  have hmap : F.map η₁ ≫ F.map θ = F.map (a.val ⊗ₘ b.val) ≫ F.map η₂ :=
    (F.map_comp η₁ θ).symm.trans ((congrArg F.map hη).trans (F.map_comp _ _))
  have hq : q₁ ≫ F.map (a.val ⊗ₘ b.val) = (F.map a.val ⊗ₘ F.map b.val) ≫ q₂ :=
    pushforwardPresheafTensorMap_naturality f a.val b.val
  change (q₁ ≫ F.map η₁) ≫ F.map θ = (F.map a.val ⊗ₘ F.map b.val) ≫ q₂ ≫ F.map η₂
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t ↦ q₁ ≫ t) hmap).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun t ↦ t ≫ F.map η₂) hq).trans (Category.assoc _ _ _))))

/-- The canonical comparison from the pullback of a tensor product to
the tensor product of the pullbacks. -/
def pullbackSheafTensorMap {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules) :
    (Scheme.Modules.pullback f).obj (SheafTensor.Construction.sheafTensor M N) ⟶
      SheafTensor.Construction.sheafTensor ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (sheafTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
      pushforwardSheafTensorMap f ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N))

theorem pullbackSheafTensorMap_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M M' N N' : Y.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    (Scheme.Modules.pullback f).map (sheafTensorMap a b) ≫ pullbackSheafTensorMap f M' N' =
      pullbackSheafTensorMap f M N ≫
        sheafTensorMap ((Scheme.Modules.pullback f).map a) ((Scheme.Modules.pullback f).map b) := by
  let L := Scheme.Modules.pullback f
  let R := Scheme.Modules.pushforward f
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  apply adj.homEquiv_naturality_right_square
  change sheafTensorMap a b ≫
      (sheafTensorMap (adj.unit.app M') (adj.unit.app N') ≫
        pushforwardSheafTensorMap f (L.obj M') (L.obj N')) =
    (sheafTensorMap (adj.unit.app M) (adj.unit.app N) ≫
      pushforwardSheafTensorMap f (L.obj M) (L.obj N)) ≫
        R.map (sheafTensorMap (L.map a) (L.map b))
  rw [Category.assoc, pushforwardSheafTensorMap_naturality, ← Category.assoc,
    ← sheafTensorMap_comp, ← Category.assoc, ← sheafTensorMap_comp]
  congr 1
  exact congrArg₂ sheafTensorMap (adj.unit.naturality a) (adj.unit.naturality b)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorFunctoriality.Construction
